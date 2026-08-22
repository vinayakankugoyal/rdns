//! Terminal dashboard showing system stats, DNS metrics, and live query logs.

use crate::{blocklist::DNSBlocklist, metrics};
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode},
};
use ratatui::{prelude::*, widgets::*};
use std::{
    collections::VecDeque,
    io,
    sync::Arc,
    time::{Duration, Instant},
};
use sysinfo::System;
use tokio::sync::broadcast;

/// Maximum number of log lines retained for display.
const MAX_LOG_LINES: usize = 50;

/// Time between UI refreshes.
const REFRESH_INTERVAL: Duration = Duration::from_millis(250);

// Tokyo Night palette.
const TN_BG: Color = Color::Rgb(26, 27, 38);
const TN_FG: Color = Color::Rgb(192, 202, 245);
const TN_RED: Color = Color::Rgb(247, 118, 142);
const TN_GREEN: Color = Color::Rgb(158, 206, 106);
const TN_YELLOW: Color = Color::Rgb(224, 175, 104);
const TN_BLUE: Color = Color::Rgb(122, 162, 247);
const TN_MAGENTA: Color = Color::Rgb(187, 154, 247);
const TN_CYAN: Color = Color::Rgb(125, 207, 255);
const TN_WHITE: Color = Color::Rgb(169, 177, 214);

/// Runs the TUI until the user quits (by pressing `q`).
pub async fn run(
    mut rx: broadcast::Receiver<String>,
    blocklist: Arc<DNSBlocklist>,
) -> io::Result<()> {
    // Set up the terminal.
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let mut sys = System::new_all();
    let mut logs = VecDeque::with_capacity(MAX_LOG_LINES);
    let start_time = Instant::now();

    let res = run_app(
        &mut terminal,
        &mut sys,
        &mut rx,
        &mut logs,
        blocklist,
        start_time,
    )
    .await;

    // Restore the terminal.
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
    logs: &mut VecDeque<String>,
    blocklist: Arc<DNSBlocklist>,
    start_time: Instant,
) -> io::Result<()> {
    let mut interval = tokio::time::interval(REFRESH_INTERVAL);

    loop {
        // Handle input without blocking.
        if crossterm::event::poll(Duration::from_millis(0))?
            && let Event::Key(key) = event::read()?
            && key.code == KeyCode::Char('q')
        {
            return Ok(());
        }

        // Drain pending log lines, keeping only the newest.
        while let Ok(log) = rx.try_recv() {
            if logs.len() >= MAX_LOG_LINES {
                logs.pop_front();
            }
            logs.push_back(log);
        }

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
    logs: &VecDeque<String>,
    blocklist: &DNSBlocklist,
    start_time: Instant,
) {
    // Paint the background for the whole area.
    let size = f.area();
    let block = Block::default().style(Style::default().bg(TN_BG));
    f.render_widget(block, size);

    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(6), // Top dashboard
            Constraint::Length(7), // Latency plot
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

    // --- Latency plot ---
    let latencies_data: Vec<(f64, f64)> = match metrics::RECENT_LATENCIES.lock() {
        Ok(l) => l
            .iter()
            .enumerate()
            .map(|(i, &v)| (i as f64, v as f64))
            .collect(),
        Err(_) => Vec::new(),
    };

    let avg_latency = if latencies_data.is_empty() {
        0.0
    } else {
        latencies_data.iter().map(|(_, v)| v).sum::<f64>() / latencies_data.len() as f64
    };

    let max_latency = latencies_data
        .iter()
        .map(|(_, v)| *v)
        .fold(0.0, f64::max)
        .max(10.0);

    let dataset = Dataset::default()
        .name("Latency")
        .marker(symbols::Marker::Braille)
        .graph_type(GraphType::Line)
        .style(Style::default().fg(TN_CYAN))
        .data(&latencies_data);

    let chart = Chart::new(vec![dataset])
        .block(
            Block::default()
                .title(Span::styled(
                    format!(
                        " Latency (Avg: {:.1}ms, Max: {:.1}ms) ",
                        avg_latency, max_latency
                    ),
                    Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD),
                ))
                .borders(Borders::ALL)
                .border_style(Style::default().fg(TN_BLUE)),
        )
        .x_axis(
            Axis::default()
                .style(Style::default().fg(TN_FG))
                .bounds([0.0, 100.0]),
        )
        .y_axis(
            Axis::default()
                .title("ms")
                .style(Style::default().fg(TN_FG))
                .bounds([0.0, max_latency * 1.1])
                .labels(vec![
                    Span::raw("0"),
                    Span::raw(format!("{:.0}", max_latency / 2.0)),
                    Span::raw(format!("{:.0}", max_latency)),
                ]),
        );

    f.render_widget(chart, chunks[1]);

    // --- System panel ---
    let uptime = start_time.elapsed().as_secs();
    let uptime_str = format!(
        "{:02}h {:02}m {:02}s",
        uptime / 3600,
        (uptime % 3600) / 60,
        uptime % 60
    );

    let global_cpu_usage = sys.global_cpu_usage();
    let memory_used = sys.used_memory() / 1024 / 1024;
    let memory_total = sys.total_memory() / 1024 / 1024;

    let sys_text = vec![
        Line::from(vec![
            Span::styled("CPU Usage: ", Style::default().fg(TN_FG)),
            Span::styled(
                format!("{:.1}%", global_cpu_usage),
                Style::default().fg(TN_GREEN),
            ),
        ]),
        Line::from(vec![
            Span::styled("RAM Usage: ", Style::default().fg(TN_FG)),
            Span::styled(
                format!("{}MB / {}MB", memory_used, memory_total),
                Style::default().fg(TN_CYAN),
            ),
        ]),
        Line::from(vec![
            Span::styled("Uptime:    ", Style::default().fg(TN_FG)),
            Span::styled(uptime_str, Style::default().fg(TN_YELLOW)),
        ]),
        Line::from(vec![
            Span::styled("Blocklist: ", Style::default().fg(TN_FG)),
            Span::styled(
                format!("{} domains", blocklist.len()),
                Style::default().fg(TN_RED),
            ),
        ]),
    ];

    let sys_block = Paragraph::new(sys_text).block(
        Block::default()
            .title(Span::styled(
                " System Resources ",
                Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD),
            ))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)),
    );
    f.render_widget(sys_block, top_chunks[0]);

    // --- Metrics panel ---
    let hits = metrics::CACHE_HITS.get();
    let misses = metrics::CACHE_MISSES.get();
    let total = hits + misses;
    let hit_rate = if total > 0.0 {
        (hits / total) * 100.0
    } else {
        0.0
    };
    let blocked = metrics::BLOCKED_REQUESTS.get();

    let metrics_text = vec![
        Line::from(vec![
            Span::styled("Total Queries:  ", Style::default().fg(TN_FG)),
            Span::styled(format!("{}", total), Style::default().fg(TN_WHITE)),
        ]),
        Line::from(vec![
            Span::styled("Cache Hits:     ", Style::default().fg(TN_FG)),
            Span::styled(
                format!("{} ({:.1}%)", hits, hit_rate),
                Style::default().fg(TN_GREEN),
            ),
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

    let metrics_block = Paragraph::new(metrics_text).block(
        Block::default()
            .title(Span::styled(
                " DNS Metrics ",
                Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD),
            ))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)),
    );
    f.render_widget(metrics_block, top_chunks[1]);

    // --- Logs panel ---
    // Newest entries are at the back of the deque; render newest first.
    let logs_items: Vec<ListItem> = logs
        .iter()
        .rev()
        .map(|m| {
            let style = if m.contains("BLOCKED") {
                Style::default().fg(TN_RED)
            } else if m.contains("CACHE HIT") {
                Style::default().fg(TN_GREEN)
            } else {
                Style::default().fg(TN_FG)
            };
            ListItem::new(Line::from(Span::styled(m.as_str(), style)))
        })
        .collect();

    let logs_list = List::new(logs_items).block(
        Block::default()
            .title(Span::styled(
                " Live Query Log ",
                Style::default().fg(TN_MAGENTA).add_modifier(Modifier::BOLD),
            ))
            .borders(Borders::ALL)
            .border_style(Style::default().fg(TN_BLUE)),
    );

    f.render_widget(logs_list, chunks[2]);
}
