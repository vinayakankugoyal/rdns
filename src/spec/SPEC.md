# rdns specification

This directory holds a specification of rdns written as executable properties.
Each property is a Rust `#[test]` next to the module it describes. A property
that holds runs in plain `cargo test`. A property the code violates today is an
`#[ignore]`d test carrying a concrete counterexample, so

```bash
cargo test                 # properties that hold
cargo test -- --ignored    # reproduce every known violation
```

When a bug is fixed, delete the `#[ignore]` line and the test then guards
against the bug coming back.

"Exhaustive" means the whole input domain was checked. "Bounded" means a fixed
seed generated the inputs, so every run checks the same cases.

## Wire codec (`packet_spec.rs`)

| ID | Property | Status |
|----|----------|--------|
| H1 | `write(read(h)) = h` for every 12-byte header | holds (exhaustive over flag bytes) |
| P1 | `from_bytes` terminates on every input | **violated** – a compression-pointer cycle recurses without bound |
| P1′ | …on inputs without pointer cycles | holds (bounded) |
| P2 | every parsed name is well formed (labels 1–63, root-terminated, ≤255 bytes) and equals the RFC 1035 §4.1.4 reference decoding | **violated** – truncated/dangling names are accepted |
| P3 | relaying preserves meaning: `parse(to_bytes(parse(m))) ≡ parse(m)` and header counts equal section lengths | holds for NS/CNAME/PTR/MX; **violated** for SOA RDATA pointers and for messages cut short |
| B1 | a synthesized blocked answer has RDATA of the right shape for its type | **violated** for AAAA, MX, TXT, HTTPS, … |
| R1 | `response_bytes` keeps the ID and question, sets QR, and ANCOUNT = number of answers | holds (bounded) |

## Cache (`cache_spec.rs`)

| ID | Property | Status |
|----|----------|--------|
| C1 | `get` after `insert` returns the answers while the entry is live | holds |
| C2 | `cleanup(now)` removes exactly the expired entries | holds |
| C3 | served TTL ≤ remaining cache lifetime | **violated** – the original TTL is served |
| C4 | TTL-0 records are not cached (RFC 1035 §3.2.1) | **violated** – everything is held ≥300s |

## Blocklist (`blocklist_spec.rs`)

| ID | Property | Status |
|----|----------|--------|
| L1 | `parse_hosts` keeps exactly the `0.0.0.0 <domain>` lines | holds |
| L2 | matching is ASCII case-insensitive (RFC 4343) | **violated** |

## Forwarder, end to end (`forwarder_spec.rs`)

These tests run a real `Server` on loopback against a scripted upstream.

| ID | Property | Status |
|----|----------|--------|
| F0 | a forwarded answer reaches the client with its own ID and is then cached | holds |
| F1 | an upstream reply is accepted and cached only if it matches the pending query's ID *and* question | **violated** – ID only, and IDs are sequential |
| F2 | no two in-flight queries share an ID, and no pending query is silently dropped | **violated** – entries never expire and IDs wrap |
| F3 | a cache hit replays the RCODE of the cached response | **violated** – NXDOMAIN/SERVFAIL are replayed as NOERROR |
| F4 | a TC=1 response is not cached as if complete | **violated** |
| F5 | a relayed message is complete or has TC=1 | **violated** – >512-byte replies are cut silently |
