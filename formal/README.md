# Lean model of rdns

A Lean 4 model of rdns's wire codec, name decoder, response serialization,
cache policy and cache key. Properties that hold are proved; properties
that fail are refuted with a concrete counterexample, keeping the
statement as strong as rdns claims it. The method follows
<https://broyojo.com/python-formalization/>:

1. **Copy.** Each Rust function is rewritten in Lean, statement by
   statement, keeping Rust's integer widths, wraparound, truncating casts
   and early returns.
2. **Test.** `differential/` runs the copy and the real code side by side
   on 200,000 generated messages. Any disagreement means the copy is wrong.
3. **Prove.** State the property rdns promises (README, `docs/SPEC.md`,
   doc comments) or an RFC requires, and have Lean check it.
4. **Check.** A second agent, which didn't write the model, reviewed it
   against the Rust code and tried to break the proofs by mutating the
   model. Its findings were fixed. `repro/e2e.py` reproduces every bug on
   the real binary.

Every proof is checked by Lean's kernel. There is no `sorry`, `native_decide`
or `bv_decide`, and `#print axioms` shows only `propext`, `Quot.sound` and
`Classical.choice`. No Mathlib, so it builds offline with just the toolchain:

```bash
lake build    # checks every proof
```

## What is proved

| Theorem | Property |
|---------|----------|
| `h1_header_roundtrip` (Wire) | **H1**: `write(read(b)) = b` for every 12-byte header |
| `readNameLoop` (Name) | **P1**: the name decoder terminates on every input. Lean only accepts the definition with a termination proof; allowing a self-pointer makes it fail to compile |
| `readName_wf` (Name) | **P2, first half**: every decoded name is well formed (labels of 1–63 bytes, then the root) and at most 255 bytes |
| `readName_consumed` (Name) | the bytes a name occupies are ≥ 1 and within the buffer |
| `no_underflow` (Name) | in every loop state where Rust evaluates `pos + 2 - start` or `pos - start`, `start ≤ pos` |
| `r1_response_header` (Packet) | **R1, header part**: QR = 1, TC = AA = 0, the given RCODE, the query's ID |
| `served_record_never_outlives_ttl` (Cache) | the TTL arithmetic: a record served at age ⌈t⌉ is dropped downstream by `max(t, its own expiry)` |
| `cd_isolation` (Forwarder) | **F8**: after any earlier queries, a CD = 0 query gets exactly the upstream's CD = 0 answer (the counterexample until [#16](https://github.com/vinayakankugoyal/rdns/issues/16) was fixed) |
| `positive_entries_never_stale` (Cache) | without `--min-cache-ttl`, a NOERROR response with answers is never served after any of its records has expired |

Not proved: the second half of P2 (`n = ref(m, i)`), P3 (completeness), and
anything about sockets, timeouts or transaction IDs.

## What is refuted

| Theorem | Property refuted | Issue |
|---------|------------------|-------|
| `bug_ad_bit_forged` (Packet) | synthesized responses never claim AD | [#15](https://github.com/vinayakankugoyal/rdns/issues/15) |
| `bug_cache_hit_loses_compression` (Packet) | a cache hit fits the client whenever the relayed response did | [#17](https://github.com/vinayakankugoyal/rdns/issues/17) |
| `bug_cname_nxdomain_stale`, `bug_cname_nodata_stale`, `bug_cname_nxdomain_drops_soa`, `bug_c4_spec_mismatch` (Cache) | records and negative answers are never served past their TTL; C4 | [#18](https://github.com/vinayakankugoyal/rdns/issues/18) |
| `bug_negative_entries_drop_nsec` (Cache) | negative entries keep their NSEC/RRSIG (RFC 2308 §5) | [#19](https://github.com/vinayakankugoyal/rdns/issues/19) |
| `bug_negative_ttl_extended` (Cache) | downstream never holds a negative answer past its negative TTL | [#20](https://github.com/vinayakankugoyal/rdns/issues/20) |
| `bug_high_bit_ttl_cached` (Cache) | TTLs ≥ 2³¹ count as 0 (RFC 2181 §8) | [#21](https://github.com/vinayakankugoyal/rdns/issues/21) |
| `bug_opcode_ignored` (Forwarder) | non-QUERY opcodes get NOTIMP | [#22](https://github.com/vinayakankugoyal/rdns/issues/22) |
| `bug_opt_missing` (Packet) | responses to EDNS queries carry OPT (RFC 6891 §7) | [#23](https://github.com/vinayakankugoyal/rdns/issues/23) |
| `c3_as_stated_is_false` (Cache) | SPEC.md's C3 as written (the spec overclaims) | [#24](https://github.com/vinayakankugoyal/rdns/issues/24) |

`bug_cache_hit_loses_compression` is the one result with a link the kernel
can't check. The kernel proves the sizes (295 bytes relayed, 825 bytes from
the cache), but can't evaluate `readName` (well-founded recursion), so the
claim that the 295-byte message parses to those records is a `#guard` run
on the compiled model. That is the same code the differential test compares
with rdns.

## Simplifications

- `Forwarder.handle` models only what the client is told: the name isn't
  blocked, the relay always succeeds, and the upstream reply always
  matches. A query with no question is modelled as SERVFAIL; Rust drops it.
- The model's `get_at` age wraps at 2³² where Rust saturates. The theorems
  assume `ageAt t < 2³²`, which holds for every live entry.
- The differential test covers `from_bytes`, `cache_ttl`, `response_bytes`,
  `truncated_bytes` and `udp_payload_limit`. It does not cover
  `insert_at`/`get_at` (private and clock-driven) or `Question` equality.

## Running the checks

```bash
lake build rdns-model
cd differential
cargo run --release -- 200000      # Lean model vs src/packet.rs and src/cache.rs
cargo run -- 200000                # the same with Rust's overflow checks on
cd ../.. && cargo build --release
python3 formal/repro/e2e.py target/release/rdns   # every bug, on the real binary
```
