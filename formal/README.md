# Lean model of rdns

A Lean 4 model of rdns's wire codec, name decoder, cache policy and
cache key, with machine-checked proofs of the properties that hold and
kernel-checked counterexamples for the ones that don't. The method follows
https://broyojo.com/python-formalization/: copy the code into Lean, test
the copy against the real code, prove properties, keep counterexamples
instead of weakening the statement.

| File | Models | Proved | Refuted (counterexample) |
|------|--------|--------|--------------------------|
| `Rdns/Wire.lean` | `Header::from_bytes`, `write_to` | H1: header roundtrip, all 2⁹⁶ headers | |
| `Rdns/Name.lean` | `read_name` | P1: terminates on every input (the definition only compiles with a termination proof); P2: every decoded name is well formed and ≤ 255 bytes; `pos - start` never underflows | |
| `Rdns/Packet.lean` | `from_bytes`, `read_record`, `response_bytes`, `truncated_bytes`, `udp_payload_limit` | R1 (header part) | `bug_ad_bit_forged`: synthesized responses copy the query's AD bit |
| `Rdns/Cache.lean` | `cache_ttl`, `insert_at`, `get_at` | served records never outlive their TTL downstream; positive answers are never served stale | negative TTL extended downstream; NXDOMAIN/NODATA behind a CNAME cached on the wrong TTL and without its SOA; C4 differs from the spec; TTLs with the top bit set are cached; C3 as stated is false |
| `Rdns/Forwarder.lean` | cache key of `handle_dns_request` | key ignores the header | `bug_cd_bypasses_validation`: one CD=1 query serves unvalidated data to CD=0 clients |

No Mathlib, so it builds offline with only the Lean toolchain:

```bash
lake build                      # check every proof
```

## Differential test

`differential/` compiles rdns's own `src/packet.rs` and `src/cache.rs`
and checks them against the Lean model on 200,000 generated messages
(parse, `cache_ttl`, `response_bytes`, `truncated_bytes`,
`udp_payload_limit`). They agree on all of them; planted mutations in the
model are caught.

```bash
lake build rdns-model
cd differential && cargo run --release -- 200000
```
