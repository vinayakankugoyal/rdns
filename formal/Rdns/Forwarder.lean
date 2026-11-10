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

RFC 4035 §3.2.2 / §4.7 and RFC 6840 §5.9: a client sets CD = 1 to ask a
validating resolver *not* to validate, and to hand back data even when its
DNSSEC is broken. The upstream rdns uses by default, 1.1.1.1, validates.
So with CD = 0 it answers SERVFAIL for a name whose signatures don't
check out, and with CD = 1 it answers with the (unvalidated) data. A
caching forwarder must not serve data it got with CD = 1 to a client that
sent CD = 0 (RFC 6840 §5.9).
-/

namespace Rdns

/-- The CD bit: bit 4 of byte 3, the low bit of Rust's `z`. -/
def Header.cd (h : Header) : Bool := h.z &&& 0x01 = 0x01

/-- The key `handle_dns_request` uses for `cache.get` and `cache.insert`. -/
def cacheKey (q : Packet) : Option Question := q.questions[0]?

/-- The cache key doesn't depend on the query header at all. -/
theorem cacheKey_ignores_header (q : Packet) (h : Header) :
    cacheKey { q with header := h } = cacheKey q := rfl

/-- One query through `handle_dns_request` (blocklist omitted: the name
isn't blocked), with a one-entry cache. `upstream cd` is the response the
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
      if k' = k then ((e.response.rcode, e.response.answers), cache)
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

end Rdns
