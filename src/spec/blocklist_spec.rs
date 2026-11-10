//! Executable specification of blocklist parsing and matching
//! (see `docs/SPEC.md`).

use super::*;

/// L1. parse_hosts keeps exactly the `0.0.0.0 <domain>` entries and
/// ignores comments, blanks and other addresses.
#[test]
fn l1_parse_hosts() {
    let body = "# comment\n\n127.0.0.1 localhost\n0.0.0.0 ads.example.com\n\
                0.0.0.0\ttracker.example.net # trailing comment\n  0.0.0.0   x.test  \n";
    let got = parse_hosts(body);
    let want: HashSet<String> = ["ads.example.com", "tracker.example.net", "x.test"]
        .map(String::from)
        .into();
    assert_eq!(got, want);
}

/// L2. Matching respects DNS name equivalence: names that differ only in
/// ASCII case are the same name (RFC 1035 §2.3.3, RFC 4343), so
/// contains(n) = contains(lowercase(n)).
///
/// Regression for #8: covers mixed-case queries, including DNS 0x20
/// randomized spellings, and mixed-case entries in the hosts file.
#[test]
fn l2_matching_ignores_case() {
    let bl = DNSBlocklist::new();
    bl.replace(parse_hosts(
        "0.0.0.0 ads.example.com\n0.0.0.0 Tracker.Example.NET\n",
    ));
    assert!(bl.contains("tracker.example.net"));
    assert!(bl.contains("ads.example.com"));
    for spelling in ["ADS.EXAMPLE.COM", "Ads.Example.Com", "aDs.eXaMpLe.cOm"] {
        assert!(bl.contains(spelling), "{spelling} not blocked");
    }
}
