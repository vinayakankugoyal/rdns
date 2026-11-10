import Rdns.Cache

/-!
# Forwarder (`src/main.rs`, `handle_dns_request`)

Only the part of `handle_dns_request` that decides *what* a client is
told is modelled: blocklist, then cache, then upstream. Sockets, timeouts
and the per-query transaction ID (F1, F2) are not.

The point of interest is the cache key. `handle_dns_request` looks up and
stores `packet.questions.first()`: name, type and class. Nothing in the
query header is part of the key, in particular not the CD
("checking disabled") bit.

RFC 4035 §3.2.2: by setting CD = 1, "the originating resolver has
indicated that it takes responsibility for performing its own
authentication", and the validating server returns the data "even if [its]
local authentication policy would reject the records". The upstream rdns
uses by default, 1.1.1.1, validates: for a name whose signatures don't
check out (e.g. `dnssec-failed.org`) it answers SERVFAIL with CD = 0 and
the unvalidated data with CD = 1. rdns doesn't validate, so the upstream's
check is the only one its clients get; caching the CD = 1 answer under the
same key hands that data to clients that never took responsibility for
it.

(RFC 6840 §5.9 says a validating cache needn't track CD, because it
validates cached data itself. rdns is not a validating cache.)
-/

namespace Rdns

/-- The CD bit: bit 4 of byte 3, the low bit of Rust's `z`. -/
def Header.cd (h : Header) : Bool := h.z &&& 0x01 = 0x01

/-- ASCII lowercase, as `to_ascii_lowercase`. -/
def asciiLower (b : UInt8) : UInt8 := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- `Question`'s `PartialEq`: type, class, and the name compared with
`eq_ignore_ascii_case` (same length, bytes equal after lowercasing). -/
def Question.same (a b : Question) : Bool :=
  a.tp == b.tp && a.cls == b.cls && a.name.size == b.name.size
    && (a.name.zip b.name).all (fun p => asciiLower p.1 == asciiLower p.2)

/-- The key `handle_dns_request` uses for `cache.get` and `cache.insert`. -/
def cacheKey (q : Packet) : Option Question := q.questions[0]?

/-- The cache key doesn't depend on the query header at all. -/
theorem cacheKey_ignores_header (q : Packet) (h : Header) :
    cacheKey { q with header := h } = cacheKey q := rfl

/-- One query through `handle_dns_request`, with a one-entry cache.
Simplified: the name isn't blocked, the relay to the client always
succeeds, the upstream's reply always matches the query (F1), and a
query with no question, which Rust drops silently, is modelled as
SERVFAIL. A cache hit reports the RCODE and records it replays, before
TTL aging. `upstream cd` is the response the
upstream resolver gives for the query's question when the query carries
that CD bit. Returns the RCODE and answers the client gets, and the new
cache. -/
def handle (cache : Option (Question × Entry)) (upstream : Bool → Packet) (q : Packet) :
    (UInt8 × Array Answer) × Option (Question × Entry) :=
  match cacheKey q with
  | none => ((RCODE_SERVFAIL, #[]), cache)  -- dropped; modelled as an error
  | some k =>
    match cache with
    | some (k', e) =>
      if k'.same k then ((e.response.rcode, e.response.answers), cache)
      else forward k
    | none => forward k
where
  forward (k : Question) :=
    let r := upstream q.header.cd
    ((r.header.rcode, r.answers),
     match insertEntry 0 r with
     | some e => some (k, e)
     | none => cache)

/-- A validating upstream and a name with broken DNSSEC: SERVFAIL, unless
the query sets CD, in which case the unvalidated record comes back. -/
def validatingUpstream (cd : Bool) : Packet :=
  if cd then resp RCODE_NOERROR #[aRec 3600] #[] else resp RCODE_SERVFAIL #[] #[]

def query (cd : Bool) : Packet :=
  { header := { (default : Header) with rd := 1, z := if cd then 0x01 else 0 }
    questions := #[{ name := nm, tp := TYPE_A, cls := 1 }]
    answers := #[], authorities := #[], resources := #[] }

/-- **CD isolation.** For any order of queries, a client that leaves CD
clear never receives data the validating upstream would have refused it:
run any queries first, then a CD = 0 query, and it gets SERVFAIL. -/
def CdIsolation : Prop :=
  ∀ earlier : List Bool,
    let cache := earlier.foldl (fun c cd => (handle c validatingUpstream (query cd)).2) none
    ((handle cache validatingUpstream (query false)).1).1 = RCODE_SERVFAIL

/-- Without rdns in the way, a CD = 0 client gets SERVFAIL... -/
example : ((handle none validatingUpstream (query false)).1).1 = RCODE_SERVFAIL := by
  decide +kernel

/-- **Counterexample.** ...but after one CD = 1 query for the same name,
every CD = 0 client gets the unvalidated record from the cache, for the
record's whole TTL. Anyone who can send rdns a query (it listens on
0.0.0.0) can switch off the upstream's DNSSEC validation for a name, for
every client. -/
theorem bug_cd_bypasses_validation : ¬ CdIsolation := fun h =>
  absurd (h [true]) (by decide +kernel)

example :
    let cache := (handle none validatingUpstream (query true)).2
    (handle cache validatingUpstream (query false)).1 = (RCODE_NOERROR, #[aRec 3600]) := by
  decide +kernel


/-- Lookups ignore case (C6): `Www.Example.com` finds `www.example.com`. -/
example : (({ name := #[3, 87, 119, 119, 0], tp := 1, cls := 1 } : Question).same
    { name := #[3, 119, 119, 119, 0], tp := 1, cls := 1 }) = true := by decide +kernel

/-! ## Opcode -/

def RCODE_NOTIMP : UInt8 := 4

/-- **RFC 1035 §4.1.1**: a server returns NOTIMP ("the name server does not
support the requested kind of query") for opcodes it doesn't implement.
rdns implements only QUERY (0). -/
def OtherOpcodesNotImp : Prop :=
  ∀ (cache : Option (Question × Entry)) (upstream : Bool → Packet) (q : Packet),
    q.header.opcode ≠ 0 → ((handle cache upstream q).1).1 = RCODE_NOTIMP

/-- **Counterexample.** An UPDATE (opcode 5) for a cached name gets the cached
answer, NOERROR. -/
theorem bug_opcode_ignored : ¬ OtherOpcodesNotImp := fun h => by
  have := h (handle none validatingUpstream (query true)).2 validatingUpstream
    { query false with header := { (query false).header with opcode := 5 } } (by decide)
  revert this; decide +kernel

end Rdns
