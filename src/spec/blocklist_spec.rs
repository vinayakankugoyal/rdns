//! Executable specification of blocklist parsing and matching
//! (see `spec/SPEC.md`).

use super::*;

/// L1. parse_hosts keeps exactly the `0.0.0.0 <domain>` entries and
/// ignores comments, blanks and other addresses.                 holds
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
/// Fails: the lookup is an exact `HashSet<String>` match, so `ADS.example.com`
/// (or any 0x20-randomized spelling, which some stub resolvers send by
/// default) sails past the blocklist.
#[test]
#[ignore = "bug: blocklist matching is case-sensitive (trivial bypass)"]
fn l2_counterexample_case_bypass() {
    let bl = DNSBlocklist::new();
    bl.replace(parse_hosts("0.0.0.0 ads.example.com\n"));
    assert!(bl.contains("ads.example.com"));
    for spelling in ["ADS.EXAMPLE.COM", "Ads.Example.Com", "aDs.eXaMpLe.cOm"] {
        assert!(bl.contains(spelling), "{spelling} not blocked");
    }
}
