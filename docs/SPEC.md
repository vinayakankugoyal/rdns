# The rdns specification

This document says precisely what rdns guarantees, and how each guarantee
is checked. It exists because writing it down found bugs: the first draft
of this spec, checked against rdns 0.1.0, turned up eleven
([#3](https://github.com/vinayakankugoyal/rdns/issues/3)–[#13](https://github.com/vinayakankugoyal/rdns/issues/13)),
including a remote crash and a cache-poisoning weakness. All eleven are
fixed, and each has a test that fails if it comes back.

A second pass modelled rdns in Lean 4 ([`formal/`](../formal)) and proved
the properties that hold. It found ten more ([#15](https://github.com/vinayakankugoyal/rdns/issues/15)–[#24](https://github.com/vinayakankugoyal/rdns/issues/24)), among them a
forged DNSSEC "authenticated" bit and a way for any client to turn off
the upstream's DNSSEC validation. These are still open, and the
properties they break are marked **✗** below. Each such property states
what rdns *should* do. None was weakened to fit the code.

- [How to read this](#how-to-read-this)
- [Definitions](#definitions)
- [1. Wire codec](#1-wire-codec)
- [2. Synthesized responses](#2-synthesized-responses)
- [3. Cache](#3-cache)
- [4. Blocklist](#4-blocklist)
- [5. Forwarder, end to end](#5-forwarder-end-to-end)
- [Bugs this spec found](#bugs-this-spec-found)
- [Bugs the Lean model found](#bugs-the-lean-model-found)
- [What this spec does not cover](#what-this-spec-does-not-cover)

## How to read this

Each property has an ID, a statement, a **check** and the test that
performs it. Tests live in [`src/spec/`](../src/spec), next to the module
they describe, and run with the rest of the suite:

```bash
cargo test
```

There are five kinds of check:

| Check | Meaning |
|-------|---------|
| **proof** | A theorem about a Lean model of the code ([`formal/`](../formal)), checked by Lean's kernel. The model is compared with the Rust code on 200,000 generated messages (`formal/differential`). |
| **exhaustive** | The whole input domain (or the whole of the part that matters) is enumerated. |
| **bounded** | A fixed-seed generator produces up to 200,000 inputs, so every run checks the same cases. |
| **witness** | Specific inputs, chosen to hit a case that once failed. |
| **argument** | A short proof in the source, backed by a test. |

A **proof** covers every input, but it is about the model, so it is only
as good as the model's fidelity. That is why the differential test exists.
An exhaustive check is as good as a proof for its domain; a bounded check
is strong evidence. **✗** marks a property rdns violates today. Its
counterexample is a Lean theorem `bug_…`, and the issue reproduces it on
the real binary. See
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
| H1 | Header codec is a bijection: `write(read(b)) = b` for every `b ∈ Byte¹²` | **proof** ([`h1_header_roundtrip`](../formal/Rdns/Wire.lean)) + exhaustive over the two flag bytes (2¹⁶ values) | `h1_header_roundtrip_exhaustive` |
| P1 | **Totality:** `parse` terminates on every input | **proof** ([`readNameLoop`](../formal/Rdns/Name.lean) is a total function) + bounded (50k random messages, pointers included) + witness (3 pointer cycles, in a child process) | `p1_parser_total_on_random_inputs`, `p1_pointer_cycles_terminate` |
| P2 | **Soundness:** if `parse(m) = p` then every name `n` in `p` has `WF(n)` and `n = ref(m, i)` for the offset `i` it was read from; the bytes it occupies lie inside `m`, and the decoder's offset arithmetic never underflows | **proof** of `WF(n)`, the bytes occupied and no underflow ([`readName_wf`, `readName_consumed`, `no_underflow`](../formal/Rdns/Name.lean)); bounded (200k random names) + witness for `n = ref(m, i)` | `p2_parsed_names_are_sound`, `p2_truncated_names_rejected`, `p2_overlong_names_rejected` |
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
constant. The Lean model is accepted only with this argument as a
termination proof (the measure `(256 − |name|, pos)` decreases
lexicographically at every step), so the argument is machine-checked.

## 2. Synthesized responses

| ID | Property | Check | Test |
|----|----------|-------|------|
| B1 | A blocked query gets a well-typed answer: A → `0.0.0.0`, AAAA → `::`, every other type → no record (NOERROR, empty) | exhaustive over all 2¹⁶ types | `b1_blocked_answers_are_well_typed_exhaustive` |
| R1 | `response_bytes` answers the query: same ID and question, QR = 1, TC = 0, the given RCODE, and section counts equal to the records written | bounded (2k) | `r1_response_bytes_shape` |
| R2 | Each served TTL is `ttl(r) ⊖ age`, where `⊖` is subtraction saturating at 0 | exhaustive over ages 0–700, plus `u32::MAX` | `r2_ttls_are_aged` |
| R3 | The truncated form of a response is TC = 1 with the question and no records (RFC 2181 §9) | witness | `r3_truncated_bytes_shape` |
| R4 | A synthesized response never has AD or Z set; CD is copied from the query (RFC 4035 §3.2.2, §3.2.3; RFC 1035 §4.1.1). rdns validates nothing, so it must not claim AD. Regression for [#15](https://github.com/vinayakankugoyal/rdns/issues/15) | **proof** ([`no_forged_ad`](../formal/Rdns/Packet.lean), every query, RCODE and record set) + exhaustive over the query's 8 Z/AD/CD combinations | `r4_synthesized_responses_never_claim_ad_exhaustive` |
| R5 | A response to a query with an OPT record carries an OPT record (RFC 6891 §7): root owner, the UDP size rdns accepts, version 0, the query's DO bit; a query without OPT gets none. Regression for [#23](https://github.com/vinayakankugoyal/rdns/issues/23) | **proof** of ARCOUNT for every query ([`opt_echoed`](../formal/Rdns/Packet.lean)) + witness for the record itself, for answers, errors and the truncated form | `r5_opt_echoed` |
| R6 | **Compression:** `response_bytes` compresses question and owner names, and names inside RDATA of the RFC 1035 types only (RFC 3597 §4, RFC 2782); the result decodes to exactly the records written. So a cache hit is no larger than the relayed response of an upstream that compresses where allowed. Regression for [#17](https://github.com/vinayakankugoyal/rdns/issues/17), where 10 SRV records relayed in 295 bytes came back from the cache in 825 | bounded (5k random record sets) + witness; the Lean model compresses identically (differential test), and the kernel checks that the 10-record SRV set now takes 455 bytes ([`cache_hit_fits_after_compression`](../formal/Rdns/Packet.lean)) | `r6_rebuilt_responses_roundtrip`, `r6_cache_hit_no_larger_than_relayed` |

## 3. Cache

Source: [`src/cache.rs`](../src/cache.rs) ·
Tests: [`src/spec/cache_spec.rs`](../src/spec/cache_spec.rs)

The cache lifetime of a response `r` is

```
cache_ttl(r) =
  ⊥                       if TC(r) = 1
  min(A(r), N(r))         if rcode(r) = NOERROR,
                             or rcode(r) = NXDOMAIN and authorities(r) has an SOA
  ⊥                       otherwise (errors; NXDOMAIN without an SOA)

where
  A(r) = min { ttl(a) | a ∈ answers(r) }             (∞ if there are no answers)
  N(r) = min(ttl(s), MINIMUM(s)) for the first SOA s in authorities(r)
                                                     (∞ if there is none)
  a TTL with the top bit set counts as 0             (RFC 2181 §8)

and is ⊥ whenever the value above is 0 or ∞.
```

where `⊥` means "don't cache" (RFC 1035 §3.2.1, RFC 2308 §5). A response
with both answers and an SOA is a negative answer reached through a CNAME
(RFC 2308 §2.1, §2.2), and both bounds apply (until [#18](https://github.com/vinayakankugoyal/rdns/issues/18) the code used
only one of them, and until [#21](https://github.com/vinayakankugoyal/rdns/issues/21) it ignored the top bit). An entry is
kept for `max(cache_ttl(r), min_cache_ttl)`, where `min_cache_ttl` is the
`--min-cache-ttl` flag (default 0).

| ID | Property | Check | Test |
|----|----------|-------|------|
| C1 | `get(q)` after `insert(q, r)` replays `r`'s answers while the entry is live | witness | `c1_insert_then_get` |
| C2 | `cleanup(t)` removes exactly the entries that have expired by `t` | witness | `c2_cleanup_removes_only_expired` |
| C3 | **Honest TTLs:** a record served at time `t` with TTL `s` is dropped downstream by `max(t, its own expiry)`, whatever `min_cache_ttl` is; and the entry is live exactly until it expires. (An earlier wording, "every served TTL ≤ the entry's remaining lifetime", is false for entries with records of different TTLs; see [#24](https://github.com/vinayakankugoyal/rdns/issues/24) and [`c3_as_stated_is_false`](../formal/Rdns/Cache.lean).) | **proof** of the TTL arithmetic ([`served_record_never_outlives_ttl`](../formal/Rdns/Cache.lean)) + exhaustive over `t` in 250 ms steps across a one-record entry's life, for `min_cache_ttl ∈ {0, 300, 1000}` | `c3_served_ttl_never_exceeds_remaining_lifetime_exhaustive` |
| C4 | The cache stores exactly what `cache_ttl` above allows | **proof** for every response ([`cacheTtl_eq_spec`](../formal/Rdns/Cache.lean); NXDOMAIN behind a CNAME and TTLs ≥ 2³¹ were the counterexamples until [#18](https://github.com/vinayakankugoyal/rdns/issues/18) and [#21](https://github.com/vinayakankugoyal/rdns/issues/21)), plus no lifetime has the top bit set ([`cacheTtl_lt`, `high_bit_ttls_not_cached`](../formal/Rdns/Cache.lean)) + witness, one case per branch | `c4_cache_ttl_policy` |
| C5 | A negative entry replays its RCODE, its SOA (TTL capped at MINIMUM, C8) and the NSEC/NSEC3/RRSIG records of its authority section (RFC 2308 §5), including when it also has answers; other authority records are dropped. Regression for [#18](https://github.com/vinayakankugoyal/rdns/issues/18) and [#19](https://github.com/vinayakankugoyal/rdns/issues/19) | **proof** for every response ([`negative_entries_keep_proofs`, `negative_entries_keep_soa`](../formal/Rdns/Cache.lean)) + witness | `c5_negative_entries_keep_rcode_and_soa`, `c5_cname_negatives_keep_soa`, `c5_negative_entries_keep_dnssec_proofs` |
| C6 | Lookups use `≡`, so names differing only in case share an entry | witness | `c6_lookups_ignore_case` |
| C7 | **Nothing stale:** with `min_cache_ttl = 0`, no record is served after its TTL and no negative answer after its negative TTL. Regression for [#18](https://github.com/vinayakankugoyal/rdns/issues/18) | **proof** for every response ([`entries_never_stale`, `negative_entries_not_stale`](../formal/Rdns/Cache.lean)) + witness, one per shape | `c7_nothing_served_stale` |
| C8 | **Honest negative TTLs:** a downstream resolver given a cached negative answer stops believing it by the time its negative TTL runs out, so the served SOA's TTL is at most `min(ttl(s), MINIMUM(s)) ⊖ age` (RFC 2308 §5): the SOA is stored with that TTL. Regression for [#20](https://github.com/vinayakankugoyal/rdns/issues/20) | **proof** for every response, `min_cache_ttl` and time ([`negative_answers_honest`](../formal/Rdns/Cache.lean)) + exhaustive over `t` in 500 ms steps for 3 SOAs × 3 `min_cache_ttl` values | `c8_negative_ttls_are_honest_exhaustive` |

C3 is what makes `--min-cache-ttl` safe. rdns may keep a record longer
than its TTL, but it then serves it with TTL 0, so no downstream cache keeps
it any longer. C8 is the same promise for negative answers, where the
deadline is carried by the SOA, not by a record of the answer.

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
| F1 | An upstream datagram is accepted only if it parses, is a response, and matches the query's ID **and** question. Anything else is ignored, never relayed and never cached. Transaction IDs are random. | `f1_mismatched_replies_ignored`, `f1_transaction_ids_are_unpredictable` |
| F2 | Every query is answered: if the upstream stays silent, the client gets SERVFAIL after the timeout. Concurrent queries never share state, so out-of-order answers reach the right clients. | `f2_unanswered_queries_get_servfail`, `f2_concurrent_queries_are_kept_apart` |
| F3 | Negative answers are replayed from the cache with their RCODE and SOA; error responses are relayed but not cached | `f3_negative_answers_keep_rcode_and_errors_are_not_cached` |
| F4 | A TC = 1 response is relayed with TC = 1 and not cached | `f4_truncated_responses_relayed_not_cached` |
| F5 | No client gets a response larger than its UDP limit (E1); a response that would exceed it becomes the truncated form (R3), and clients advertising a larger size get the whole response. Upstream replies are read into a 64 KiB buffer, so none is ever cut short, whatever size the client advertised | `f5_large_responses_respect_client_limit` |
| F6 | A relayed response is byte-for-byte the upstream's apart from the ID, so record types rdns doesn't understand pass through intact | `f6_relay_is_verbatim` |
| F7 | Blocked names are answered locally, in any case, with a well-typed answer (B1, L2) | `f7_blocking` |
| F8 | **CD isolation:** a client that leaves CD clear never gets data the upstream would only return with CD set, i.e. data that failed the upstream's DNSSEC validation (RFC 4035 §3.2.2). Answers to CD = 1 queries are relayed but not cached. Regression for [#16](https://github.com/vinayakankugoyal/rdns/issues/16) | `f8_cd_answers_are_not_cached`; **proof** ([`cd_isolation`](../formal/Rdns/Forwarder.lean): after any earlier queries, a CD = 0 query gets exactly the upstream's CD = 0 answer) |
| F9 | A client that leaves DO clear gets no RRSIG, NSEC or NSEC3 records it didn't ask for, and one that sets DO is never served an answer fetched without them (RFC 4035 §3.2.1): cache entries are keyed by the question and the DO bit. Regression for [#19](https://github.com/vinayakankugoyal/rdns/issues/19) | `f9_do_answers_are_kept_apart`, `c9_entries_are_keyed_by_do`; **proof** that an entry for one DO bit never answers the other ([`do_isolation`](../formal/Rdns/Forwarder.lean)) |
| F10 | A message with an opcode other than QUERY gets NOTIMP and is neither answered from the cache or blocklist nor forwarded (RFC 1035 §4.1.1). Regression for [#22](https://github.com/vinayakankugoyal/rdns/issues/22) | `f10_other_opcodes_get_notimp`; **proof** ([`other_opcodes_notimp`](../formal/Rdns/Forwarder.lean), whatever is cached) |

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

To check that the tests can actually fail, each of the 16 fixes was
reverted on its own and the suite re-run (mutation testing). The first
round caught 15 of the 16. The survivor was the switch from a counter to
random transaction IDs: F1′ then only checked that IDs weren't
*consecutive*, and other tests running in parallel shared the counter and
put gaps in the sequence. F1′ now checks that consecutive IDs are far
apart, which a counter can't satisfy, and all 16 reverts are caught. Two of
them (disabling the backward-pointer rule, and the 255-byte limit) make
the parser loop forever. The suite detects this by hanging, which is why
P1's cycle witnesses run in a child process.

## Bugs the Lean model found

Against `70e3552` (rdns after PR #14). Each issue reproduces the bug on
the real binary ([`formal/repro/e2e.py`](../formal/repro/e2e.py)) and links its
Lean counterexample.

| Issue | Property | What is wrong | Severity |
|-------|----------|---------------|----------|
| [#15](https://github.com/vinayakankugoyal/rdns/issues/15) | R4 | Cached, blocked and SERVFAIL responses copy the query's AD bit (`dig` sets it by default), claiming DNSSEC validation rdns never did | medium |
| [#16](https://github.com/vinayakankugoyal/rdns/issues/16) | F8 | The cache ignores CD, so one CD = 1 query from anyone turns off the upstream's DNSSEC validation for a name, for every client | medium |
| [#17](https://github.com/vinayakankugoyal/rdns/issues/17) | R6 | Cache hits are written without name compression, so a response that fit in 512 bytes comes back as TC = 1 from the cache | medium |
| [#18](https://github.com/vinayakankugoyal/rdns/issues/18) | C4, C5, C7 | NXDOMAIN/NODATA behind a CNAME are cached on the wrong TTL and replayed without their SOA | low–medium |
| [#19](https://github.com/vinayakankugoyal/rdns/issues/19) | C5, F9 | Negative entries drop NSEC/RRSIG; RRSIGs are served to DO = 0 clients | low–medium |
| [#20](https://github.com/vinayakankugoyal/rdns/issues/20) | C8 | A cached SOA's TTL isn't capped at MINIMUM, so downstream negative caching restarts | low |
| [#21](https://github.com/vinayakankugoyal/rdns/issues/21) | C4 | TTLs with the top bit set are cached for up to 136 years | low |
| [#22](https://github.com/vinayakankugoyal/rdns/issues/22) | F10 | Non-QUERY opcodes are answered from the cache instead of NOTIMP | low |
| [#23](https://github.com/vinayakankugoyal/rdns/issues/23) | R5 | Synthesized responses to EDNS queries omit OPT | low |
| [#24](https://github.com/vinayakankugoyal/rdns/issues/24) | C3 | C3 was stated too strongly (spec bug; the code was fine) | docs |

The model was checked the way the tests were. A second agent that hadn't
written it compared it with the Rust code and mutated it to see whether the
proofs still passed. That found three proofs weaker than their
descriptions; they were strengthened. It also found [#17](https://github.com/vinayakankugoyal/rdns/issues/17). Planted bugs in
the model are caught by the differential test, and a self-pointer in the
name decoder makes the model fail to compile.

## What this spec does not cover

- **Proofs of everything.** H1, P1, half of P2, C3's arithmetic, C4 and C7
  are proved in Lean; the rest are tests. A proof is about
  the Lean model, which is compared with the Rust code by differential
  testing, not derived from it. The model leaves out sockets, timeouts and
  transaction IDs (F1, F2). Bounded checks don't cover their whole domain,
  so a bug in a case no generator reaches could survive.
- **TCP.** rdns serves UDP only. Truncated responses tell clients to retry
  over TCP, which rdns doesn't offer.
- **DNSSEC validation.** rdns doesn't validate. It relays DNSSEC records
  verbatim (F6), and must not claim or undermine validation it doesn't do
  (R4, F8, F9).
- **Resource limits.** The cache isn't bounded in size, and nothing limits
  query rate.
- **The TUI, metrics endpoint and blocklist download** are outside the
  spec.
