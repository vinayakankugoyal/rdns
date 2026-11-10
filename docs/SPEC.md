# The rdns specification

This document says precisely what rdns guarantees, and how each guarantee
is checked. It exists because writing it down found bugs: the first draft
of this spec, checked against rdns 0.1.0, turned up eleven
([#3](https://github.com/vinayakankugoyal/rdns/issues/3)–[#13](https://github.com/vinayakankugoyal/rdns/issues/13)),
including a remote crash and a cache-poisoning weakness. Every property
below now holds, and each has a test that fails if it stops holding.

- [How to read this](#how-to-read-this)
- [Definitions](#definitions)
- [1. Wire codec](#1-wire-codec)
- [2. Synthesized responses](#2-synthesized-responses)
- [3. Cache](#3-cache)
- [4. Blocklist](#4-blocklist)
- [5. Forwarder, end to end](#5-forwarder-end-to-end)
- [Bugs this spec found](#bugs-this-spec-found)
- [What this spec does not cover](#what-this-spec-does-not-cover)

## How to read this

Each property has an ID, a statement, a **check** and the test that
performs it. Tests live in [`src/spec/`](../src/spec), next to the module
they describe, and run with the rest of the suite:

```bash
cargo test
```

There are four kinds of check:

| Check | Meaning |
|-------|---------|
| **exhaustive** | The whole input domain (or the whole of the part that matters) is enumerated. |
| **bounded** | A fixed-seed generator produces up to 200,000 inputs, so every run checks the same cases. |
| **witness** | Specific inputs, chosen to hit a case that once failed. |
| **argument** | A short proof in the source, backed by a test. |

These are checks, not machine-verified proofs. An exhaustive check is as
good as a proof for its domain; a bounded check is strong evidence. See
[What this spec does not cover](#what-this-spec-does-not-cover).

## Definitions

**Messages.** A message is a byte string `m ∈ Byte*`. Parsing is a
function

```
parse : Byte* → Packet ∪ {⊥}
```

(`DNSPacket::from_bytes`, returning `None` for `⊥`). A message is
*rejected* when `parse(m) = ⊥`.

**Names.** A name in uncompressed wire format is a sequence of labels, each
a length byte `1..=63` followed by that many bytes, ending with the root
label `0`. The predicate

```
WF(n)  ⇔  n = ℓ₁ ⋯ ℓₖ · 0,   1 ≤ |ℓᵢ| − 1 ≤ 63,   |n| ≤ 255
```

says `n` is well formed (RFC 1035 §2.3.4, §3.1).

**Reference decoding.** `ref(m, i)` is the name at offset `i` in `m` as
RFC 1035 §4.1.4 defines it: labels are read in order, and a byte with the
top two bits set starts a pointer to the 14-bit offset it encodes. `ref`
is undefined if decoding runs off the end of `m`, uses a reserved label
type, or loops. The spec's copy is `reference_name` in
`packet_spec.rs`. It is deliberately naive, so it is easy to check by eye.

**Name equality.** `n ≡ n′` when the names are equal ignoring ASCII case
(RFC 4343). `Question` implements `Eq` and `Hash` with `≡`.

**Time.** `ttl(r)` is a record's TTL in seconds; `age(e, t)` is how long
cache entry `e` has existed at time `t`, rounded up to whole seconds.

## 1. Wire codec

Source: [`src/packet.rs`](../src/packet.rs) ·
Tests: [`src/spec/packet_spec.rs`](../src/spec/packet_spec.rs)

| ID | Property | Check | Test |
|----|----------|-------|------|
| H1 | Header codec is a bijection: `write(read(b)) = b` for every `b ∈ Byte¹²` | exhaustive over the two flag bytes (2¹⁶ values) | `h1_header_roundtrip_exhaustive` |
| P1 | **Totality:** `parse` terminates on every input | argument + bounded (50k random messages, pointers included) + witness (3 pointer cycles, in a child process) | `p1_parser_total_on_random_inputs`, `p1_pointer_cycles_terminate` |
| P2 | **Soundness:** if `parse(m) = p` then every name `n` in `p` has `WF(n)` and `n = ref(m, i)` for the offset `i` it was read from | bounded (200k random names) + witness | `p2_parsed_names_are_sound`, `p2_truncated_names_rejected`, `p2_overlong_names_rejected` |
| P3 | **Completeness:** every message whose names are well formed and compressed only with backward pointers is accepted, and each name decodes to the name that was encoded | bounded (5k random messages with suffix compression) | `p3_well_formed_messages_parse` |
| P4 | **Self-contained records:** names inside the RDATA of NS, MD, MF, CNAME, SOA, MB, MG, MR, PTR, MINFO, MX, RP, AFSDB, RT and SRV are decompressed; a record copied into another message decodes to the same thing; RDATA whose fields don't exactly fill RDLENGTH is rejected | witness | `p4_soa_rdata_is_self_contained`, `p4_name_bearing_rdata_is_decompressed`, `p4_rdata_length_mismatch_rejected` |
| P5 | **No partial parses:** every proper prefix of a valid message is rejected | exhaustive over all prefixes | `p5_truncated_sections_rejected_exhaustive` |
| Q1 | `Question` equality is `≡` on names (plus type and class), and hashing agrees with it | witness | `q1_question_equality_ignores_case` |
| E1 | A client's UDP limit is its EDNS payload size clamped to `[512, 4096]`, or 512 without EDNS (RFC 6891 §6.2.3) | witness | `e1_udp_payload_limit` |

**Why P1 holds.** `read_name` accepts a pointer only if it points strictly
backwards (RFC 1035: a pointer refers to a *prior* occurrence) and stops at
255 bytes of output. Each step of its loop either appends a label, which the
255-byte limit bounds, or jumps to a strictly smaller offset, so pointers
alone can't repeat. The loop therefore runs at most
`255 + |m|` times. It is a loop rather than recursion, so stack depth is
constant.

## 2. Synthesized responses

| ID | Property | Check | Test |
|----|----------|-------|------|
| B1 | A blocked query gets a well-typed answer: A → `0.0.0.0`, AAAA → `::`, every other type → no record (NOERROR, empty) | exhaustive over all 2¹⁶ types | `b1_blocked_answers_are_well_typed_exhaustive` |
| R1 | `response_bytes` answers the query: same ID and question, QR = 1, TC = 0, the given RCODE, and section counts equal to the records written | bounded (2k) | `r1_response_bytes_shape` |
| R2 | Each served TTL is `ttl(r) ⊖ age`, where `⊖` is subtraction saturating at 0 | exhaustive over ages 0–700, plus `u32::MAX` | `r2_ttls_are_aged` |
| R3 | The truncated form of a response is TC = 1 with the question and no records (RFC 2181 §9) | witness | `r3_truncated_bytes_shape` |

## 3. Cache

Source: [`src/cache.rs`](../src/cache.rs) ·
Tests: [`src/spec/cache_spec.rs`](../src/spec/cache_spec.rs)

The cache lifetime of a response `r` is

```
cache_ttl(r) =
  ⊥                                  if TC(r) = 1
  min { ttl(a) | a ∈ answers(r) }    if rcode(r) = NOERROR and answers(r) ≠ ∅
  min(ttl(s), MINIMUM(s))            if rcode(r) ∈ {NOERROR, NXDOMAIN}, answers(r) = ∅,
                                        and s is an SOA in authorities(r)
  ⊥                                  otherwise (errors; negative answers without an SOA)

and is ⊥ whenever the value above is 0.
```

where `⊥` means "don't cache" (RFC 1035 §3.2.1, RFC 2308 §5). An entry is
kept for `max(cache_ttl(r), min_cache_ttl)`, where `min_cache_ttl` is the
`--min-cache-ttl` flag (default 0).

| ID | Property | Check | Test |
|----|----------|-------|------|
| C1 | `get(q)` after `insert(q, r)` replays `r`'s answers while the entry is live | witness | `c1_insert_then_get` |
| C2 | `cleanup(t)` removes exactly the entries that have expired by `t` | witness | `c2_cleanup_removes_only_expired` |
| C3 | **Honest TTLs:** at any time `t` the entry is live, every served TTL ≤ its remaining lifetime; and the entry is live exactly until it expires | exhaustive over `t` in 250 ms steps across the entry's life, for `min_cache_ttl ∈ {0, 300, 1000}` | `c3_served_ttl_never_exceeds_remaining_lifetime_exhaustive` |
| C4 | The cache stores exactly what `cache_ttl` above allows | witness, one case per branch | `c4_cache_ttl_policy` |
| C5 | A negative entry replays its RCODE and SOA | witness | `c5_negative_entries_keep_rcode_and_soa` |
| C6 | Lookups use `≡`, so names differing only in case share an entry | witness | `c6_lookups_ignore_case` |

C3 is what makes `--min-cache-ttl` safe. rdns may keep a record longer
than its TTL, but it then serves it with TTL 0, so no downstream cache keeps
it any longer.

## 4. Blocklist

Source: [`src/blocklist.rs`](../src/blocklist.rs) ·
Tests: [`src/spec/blocklist_spec.rs`](../src/spec/blocklist_spec.rs)

| ID | Property | Check | Test |
|----|----------|-------|------|
| L1 | `parse_hosts` keeps exactly the `0.0.0.0 <domain>` lines, ignoring comments, blank lines and other addresses | witness | `l1_parse_hosts` |
| L2 | `contains(n) = contains(lowercase(n))`, for entries and queries in any case | witness | `l2_matching_ignores_case` |

## 5. Forwarder, end to end

Source: [`src/main.rs`](../src/main.rs) ·
Tests: [`src/spec/forwarder_spec.rs`](../src/spec/forwarder_spec.rs)

These tests run the real request handler on loopback sockets against a
scripted upstream resolver and client.

| ID | Property | Test |
|----|----------|------|
| F0 | A forwarded answer reaches the client under the client's own ID, and the next query for the same name, in any case, is served from the cache | `f0_forward_then_cache_hit` |
| F1 | An upstream datagram is accepted only if it parses, is a response, and matches the query's ID **and** question. Anything else is ignored, never relayed and never cached. Transaction IDs are random. | `f1_mismatched_replies_ignored`, `f1_transaction_ids_are_not_sequential` |
| F2 | Every query is answered: if the upstream stays silent, the client gets SERVFAIL after the timeout. Concurrent queries never share state, so out-of-order answers reach the right clients. | `f2_unanswered_queries_get_servfail`, `f2_concurrent_queries_are_kept_apart` |
| F3 | Negative answers are replayed from the cache with their RCODE and SOA; error responses are relayed but not cached | `f3_negative_answers_keep_rcode_and_errors_are_not_cached` |
| F4 | A TC = 1 response is relayed with TC = 1 and not cached | `f4_truncated_responses_relayed_not_cached` |
| F5 | No client gets a response larger than its UDP limit (E1); a response that would exceed it becomes the truncated form (R3), and clients advertising a larger size get the whole response | `f5_large_responses_respect_client_limit` |
| F6 | A relayed response is byte-for-byte the upstream's apart from the ID, so record types rdns doesn't understand pass through intact | `f6_relay_is_verbatim` |
| F7 | Blocked names are answered locally, in any case, with a well-typed answer (B1, L2) | `f7_blocking` |

How F1 and F2 are achieved: each forwarded query uses its own UDP socket,
on a port the kernel picks, connected to the resolver so that the kernel
discards datagrams from any other address. Its transaction ID comes from a
CSPRNG. There is no shared table of pending queries, so nothing can leak,
wrap or collide, and the timeout bounds every query's lifetime.

## Bugs this spec found

Against rdns 0.1.0 (commit `20614d9`):

| Issue | Property | What was wrong |
|-------|----------|----------------|
| [#3](https://github.com/vinayakankugoyal/rdns/issues/3) | P1 | A compression-pointer cycle made the name parser recurse without bound, overflowing the stack and aborting the process |
| [#4](https://github.com/vinayakankugoyal/rdns/issues/4) | P2 | Truncated or dangling names were accepted, with TYPE/CLASS read from whatever bytes followed |
| [#5](https://github.com/vinayakankugoyal/rdns/issues/5) | P4, F6 | Re-serializing relayed responses moved offsets under SOA RDATA pointers, corrupting them |
| [#6](https://github.com/vinayakankugoyal/rdns/issues/6) | P5, F5 | Responses over 512 bytes were cut silently and relayed with header counts that didn't match their records |
| [#7](https://github.com/vinayakankugoyal/rdns/issues/7) | B1 | Blocked AAAA/MX/TXT/… queries got 4 bytes of A-shaped RDATA |
| [#8](https://github.com/vinayakankugoyal/rdns/issues/8) | L2, C6 | Blocklist matching was case-sensitive |
| [#9](https://github.com/vinayakankugoyal/rdns/issues/9) | F1 | Upstream replies were matched on a sequential ID alone, and the reply's own question was cached |
| [#10](https://github.com/vinayakankugoyal/rdns/issues/10) | F2 | Pending queries never expired, and the ID counter wrapped onto in-flight queries |
| [#11](https://github.com/vinayakankugoyal/rdns/issues/11) | C4, C5, F3 | NXDOMAIN and SERVFAIL were cached for 300 s and replayed as NOERROR |
| [#12](https://github.com/vinayakankugoyal/rdns/issues/12) | C4, F4 | TC = 1 responses were cached and replayed without TC |
| [#13](https://github.com/vinayakankugoyal/rdns/issues/13) | C3, C4 | Cached records were served with their original TTL, and TTL-0 records were cached for 5 minutes |

The spec also caught two bugs in the first draft of the fixes. Both were
underflows in `read_name`, in its bookkeeping for how many bytes a
compressed name occupies: `unwrap_or(pos - start)` evaluates
`pos - start` eagerly, even after a backward pointer has made `pos < start`.
P1's random inputs and P3's compressed messages each found one.

To check that the tests can actually fail, each fix was reverted one at a
time and the suite re-run. Every reverted fix was caught by at least one
property.

## What this spec does not cover

- **Proofs.** The checks are tests in Rust, not proofs in a theorem prover.
  Exhaustive checks cover their whole domain; bounded checks don't, so a
  bug in a case no generator reaches could survive. The argument for P1 is
  written in the source, not machine-checked.
- **TCP.** rdns serves UDP only. Truncated responses tell clients to retry
  over TCP, which rdns doesn't offer.
- **DNSSEC.** rdns doesn't validate. It relays DNSSEC records verbatim
  (F6), but synthesized and cached responses carry no signatures.
- **Resource limits.** The cache isn't bounded in size, and nothing limits
  query rate.
- **The TUI, metrics endpoint and blocklist download** are outside the
  spec.
