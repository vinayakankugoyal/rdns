use std::{io, sync::Arc, time::{Duration, Instant}};
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{prelude::*, widgets::*};
use sysinfo::System;
use tokio::sync::broadcast;
use crate::{blocklist::DNSBlocklist, metrics};

// Tokyo Night Palette
const TN_BG: Color = Color::Rgb(26, 27, 38);
const TN_FG: Color = Color::Rgb(192, 202, 245);
const TN_RED: Color = Color::Rgb(247, 118, 142);
const TN_GREEN: Color = Color::Rgb(158, 206, 106);
const TN_YELLOW: Color = Color::Rgb(224, 175, 104);
const TN_BLUE: Color = Color::Rgb(122, 162, 247);
const TN_MAGENTA: Color = Color::Rgb(187, 154, 247);
const TN_CYAN: Color = Color::Rgb(125, 207, 255);
const TN_WHITE: Color = Color::Rgb(169, 177, 214);

pub async fn run(
    mut rx: broadcast::Receiver<String>,
    blocklist: Arc<DNSBlocklist>,
) -> io::Result<()> {
    // Setup terminal
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    // State
    let mut sys = System::new_all();
    let mut logs: Vec<String> = Vec::new();
    let start_time = Instant::now();

    let res = run_app(&mut terminal, &mut sys, &mut rx, &mut logs, blocklist, start_time).await;

    // Restore terminal
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(err) = res {
        println!("{:?}", err)
    }

    Ok(())
}

async fn run_app(
    terminal: &mut Terminal<CrosstermBackend<io::Stdout>>,
    sys: &mut System,
    rx: &mut broadcast::Receiver<String>,
    logs: &mut Vec<String>,
    blocklist: Arc<DNSBlocklist>,
    start_time: Instant,
) -> io::Result<()> {
    let mut interval = tokio::time::interval(Duration::from_millis(250));

    loop {
        // Handle input (non-blocking)
        if crossterm::event::poll(Duration::from_millis(0))? {
             if let Event::Key(key) = event::read()? {
                if let KeyCode::Char('q') = key.code {
                    return Ok(());
                }
            }
        }

        // Process logs
        while let Ok(log) = rx.try_recv() {
            logs.push(log);
            if logs.len() > 50 {
                logs.remove(0);
            }
        }

        // Update system stats
        sys.refresh_cpu_all();
        sys.refresh_memory();

        terminal.draw(|f| {
             ui(f, sys, logs, &blocklist, start_time);
        })?;

        interval.tick().await;
    }
}

fn ui(
    f: &mut Frame,
    sys: &System,
    logs: &[String],
    blocklist: &DNSBlocklist,
    start_time: Instant,
) {
    // Set background color for the whole area
    let size = f.area();
    let block = Block::default().style(Style::default().bg(TN_BG));
    f.render_widget(block, size);

    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(6), // Top dashboard
            Constraint::Length(7), // Latency Plot
            Constraint::Min(10),   // Logs
        ])
        .split(f.area());

    let top_chunks = Layout::default()
        .direction(Direction::Horizontal)
        .constraints([
            Constraint::Percentage(50), // System
            Constraint::Percentage(50), // Metrics
        ])
        .split(chunks[0]);

    // --- LATENCY PLOT ---
    let latencies_data: Vec<(f64, f64)> = if let Ok(l) = metrics::RECENT_LATENCIES.lock() {
        l.iter().enumerate().map(|(i, &v)| (i as f64, v as f64)).collect()
    } else {
        vec![]
    };

    let avg_latency = if !latencies_data.is_empty() {
        latencies_data.iter().map(|(_, v)| v).sum::<f64>() / latencies_data.len() as f64
    } else {
        0.0
    };

    let max_latency = latencies_data.iter().map(|(_, v)| *v).fold(0.0, f64::max).max(10.0);

    let dataset = Dataset::default()
        .name("Latency")
        .marker(symbols::Marker::Braille)
        .graph_type(GraphType::Line)
        .style(Style::default().fg(TN_CYAN))
        .data(&latencies_data);

    let chart = Chart::new(vec![dataset])
        .block(Block::default()
            .title(Span::styled(format!(" Latency (Avg: {:.1}ms, Max: {:.1}ms) ", avg_latency, max_latency), Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD)))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)))
        .x_axis(Axis::default()
            .style(Style::default().fg(TN_FG))
            .bounds([0.0, 100.0]))
        .y_axis(Axis::default()
            .title("ms")
            .style(Style::default().fg(TN_FG))
            .bounds([0.0, max_latency * 1.1])
            .labels(vec![
                Span::raw("0"),
                Span::raw(format!("{:.0}", max_latency / 2.0)),
                Span::raw(format!("{:.0}", max_latency)),
            ]));
    
    f.render_widget(chart, chunks[1]);


    // --- SYSTEM PANEL ---
    let uptime = start_time.elapsed().as_secs();
    let uptime_str = format!("{:02}h {:02}m {:02}s", uptime / 3600, (uptime % 3600) / 60, uptime % 60);
    
    // Calculate global CPU usage (average of all CPUs)
    let global_cpu_usage = sys.global_cpu_usage();
    let memory_used = sys.used_memory() / 1024 / 1024;
    let memory_total = sys.total_memory() / 1024 / 1024;

    let sys_text = vec![
        Line::from(vec![
            Span::styled("CPU Usage: ", Style::default().fg(TN_FG)),
            Span::styled(format!("{:.1}%", global_cpu_usage), Style::default().fg(TN_GREEN)),
        ]),
        Line::from(vec![
            Span::styled("RAM Usage: ", Style::default().fg(TN_FG)),
            Span::styled(format!("{}MB / {}MB", memory_used, memory_total), Style::default().fg(TN_CYAN)),
        ]),
        Line::from(vec![
            Span::styled("Uptime:    ", Style::default().fg(TN_FG)),
            Span::styled(uptime_str, Style::default().fg(TN_YELLOW)),
        ]),
        Line::from(vec![
            Span::styled("Blocklist: ", Style::default().fg(TN_FG)),
            Span::styled(format!("{} domains", blocklist.len()), Style::default().fg(TN_RED)),
        ]),
    ];

    let sys_block = Paragraph::new(sys_text)
        .block(Block::default()
            .title(Span::styled(" System Resources ", Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD)))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)));
    f.render_widget(sys_block, top_chunks[0]);

    // --- METRICS PANEL ---
    let hits = metrics::CACHE_HITS.get();
    let misses = metrics::CACHE_MISSES.get();
    let total = hits + misses;
    let hit_rate = if total > 0.0 { (hits / total) * 100.0 } else { 0.0 };
    let blocked = metrics::BLOCKED_REQUESTS.get();
    
    // Calculate average response time
    // Histogram count and sum are internal, prometheus crate exposes them differently.
    // We can't easily get the exact "average" from the histogram object directly without accessing private fields 
    // or scraping the output. For now, we will display the count in the histogram or just blocked/total.
    // Let's rely on hit rate and total counts which are most important.
    
    let metrics_text = vec![
        Line::from(vec![
            Span::styled("Total Queries:  ", Style::default().fg(TN_FG)),
            Span::styled(format!("{}", total), Style::default().fg(TN_WHITE)),
        ]),
        Line::from(vec![
            Span::styled("Cache Hits:     ", Style::default().fg(TN_FG)),
            Span::styled(format!("{} ({:.1}%)", hits, hit_rate), Style::default().fg(TN_GREEN)),
        ]),
         Line::from(vec![
            Span::styled("Cache Misses:   ", Style::default().fg(TN_FG)),
            Span::styled(format!("{}", misses), Style::default().fg(TN_YELLOW)),
        ]),
        Line::from(vec![
            Span::styled("Blocked:        ", Style::default().fg(TN_FG)),
            Span::styled(format!("{}", blocked), Style::default().fg(TN_RED)),
        ]),
    ];

    let metrics_block = Paragraph::new(metrics_text)
        .block(Block::default()
            .title(Span::styled(" DNS Metrics ", Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD)))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)));
    f.render_widget(metrics_block, top_chunks[1]);


    // --- LOGS PANEL ---
    let logs_items: Vec<ListItem> = logs
        .iter()
        .rev() // Show newest at top/bottom depending on preference. Let's do standard log style (append to bottom).
        // Actually, for a fixed window, usually we scroll. 
        // Let's just take the last N items.
        .map(|m| {
            let style = if m.contains("BLOCKED") {
                Style::default().fg(TN_RED)
            } else if m.contains("CACHE HIT") {
                Style::default().fg(TN_GREEN)
            } else {
                Style::default().fg(TN_FG)
            };
            ListItem::new(Line::from(Span::styled(m, style)))
        })
        .collect();

    // Reverse the list back if we want to display "newest at bottom" but we gathered them in order.
    // Actually, `logs` has newest at end. `List` renders top to bottom.
    // So if we want auto-scroll, we usually render the last N.
    // We already sliced logs to 50 max.
    
    let logs_list = List::new(logs_items)
        .block(Block::default()
            .title(Span::styled(" Live Query Log ", Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD)))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)));
    
    f.render_widget(logs_list, chunks[2]);
}
