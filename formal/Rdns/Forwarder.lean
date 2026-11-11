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

def RCODE_NOTIMP : UInt8 := 4

/-- The CD bit: bit 4 of byte 3, the low bit of Rust's `z`. -/
def Header.cd (h : Header) : Bool := h.z &&& 0x01 = 0x01

/-- ASCII lowercase, as `to_ascii_lowercase`. -/
def asciiLower (b : UInt8) : UInt8 := if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

/-- `Question`'s `PartialEq`: type, class, and the name compared with
`eq_ignore_ascii_case` (same length, bytes equal after lowercasing). -/
def Question.same (a b : Question) : Bool :=
  a.tp == b.tp && a.cls == b.cls && a.name.size == b.name.size
    && (a.name.zip b.name).all (fun p => asciiLower p.1 == asciiLower p.2)

/-- The key `handle_dns_request` uses for `cache.get` and `cache.insert`:
the first question and the query's DO bit (#19). -/
def cacheKey (q : Packet) : Option (Question × Bool) := q.questions[0]?.map (·, q.dnssecOk)

/-- Key equality: `Question`'s case-insensitive `Eq`, and the DO bit. -/
def keySame (a b : Question × Bool) : Bool := a.1.same b.1 && a.2 == b.2

/-- The cache key doesn't depend on the query header at all. (DO lives in
the OPT record, not the header.) -/
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
def handle (cache : Option ((Question × Bool) × Entry)) (upstream : Bool → Packet) (q : Packet) :
    (UInt8 × Array Answer) × Option ((Question × Bool) × Entry) :=
  -- Only standard queries are served; anything else gets NOTIMP (#22).
  if q.header.opcode ≠ 0 then ((RCODE_NOTIMP, #[]), cache) else
  match cacheKey q with
  | none => ((RCODE_SERVFAIL, #[]), cache)  -- dropped; modelled as an error
  | some k =>
    match cache with
    | some (k', e) =>
      if keySame k' k then ((e.response.rcode, e.response.answers), cache)
      else forward k
    | none => forward k
where
  forward (k : Question × Bool) :=
    let r := upstream q.header.cd
    ((r.header.rcode, r.answers),
     -- Answers to CD = 1 queries are relayed but not cached (#16).
     if q.header.cd then cache
     else match insertEntry 0 r with
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

/-- Without rdns in the way, a CD = 0 client gets SERVFAIL. -/
example : ((handle none validatingUpstream (query false)).1).1 = RCODE_SERVFAIL := by
  decide +kernel

/-! ### CD isolation, in general

The theorem below is stronger than `CdIsolation`: for *any* upstream and
*any* earlier queries (any header bits, any CD), a client that leaves CD
clear gets exactly what the upstream answers with CD clear, no matter
what earlier clients asked. -/

theorem insertEntry_replays {r : Packet} {e : Entry} (h : insertEntry 0 r = some e) :
    e.response.rcode = r.header.rcode ∧ e.response.answers = r.answers := by
  unfold insertEntry at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- Every cache entry was obtained with CD clear. -/
def FromCd0 (upstream : Bool → Packet) (cache : Option ((Question × Bool) × Entry)) : Prop :=
  ∀ k e, cache = some (k, e) → insertEntry 0 (upstream false) = some e

theorem handle_keeps_FromCd0 (upstream : Bool → Packet) (cache : Option ((Question × Bool) × Entry))
    (q : Packet) (h : FromCd0 upstream cache) : FromCd0 upstream (handle cache upstream q).2 := by
  have hf : ∀ k, FromCd0 upstream (handle.forward cache upstream q k).2 := by
    intro k k' e he
    simp only [handle.forward] at he
    split at he
    · exact h k' e he
    · next hcd =>
      split at he
      · next e' hins =>
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        simpa [hcd] using hins
      · exact h k' e he
  unfold handle
  split
  · exact h  -- not a QUERY: the cache is untouched
  · split
    · exact h
    · split
      · split
        · exact h
        · exact hf _
      · exact hf _

theorem foldl_FromCd0 (upstream : Bool → Packet) (l : List Packet) :
    ∀ c, FromCd0 upstream c → FromCd0 upstream (l.foldl (fun c p => (handle c upstream p).2) c) := by
  induction l with
  | nil => intro c h; exact h
  | cons p ps ih => intro c h; exact ih _ (handle_keeps_FromCd0 upstream c p h)

/-- One CD = 0 query against a cache that holds only CD = 0 answers. -/
theorem cd0_answer (upstream : Bool → Packet) (cache : Option ((Question × Bool) × Entry)) (q : Packet)
    (hinv : FromCd0 upstream cache) (hop : q.header.opcode = 0) (hcd : q.header.cd = false)
    (hq : (cacheKey q).isSome) :
    (handle cache upstream q).1 = ((upstream false).header.rcode, (upstream false).answers) := by
  have hfwd : ∀ c k, (handle.forward c upstream q k).1
      = ((upstream false).header.rcode, (upstream false).answers) := by
    intro c k; simp [handle.forward, hcd]
  unfold handle
  simp only [hop, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · next hk => simp [hk] at hq
  · cases hc : cache with
    | none => exact hfwd _ _
    | some ke =>
      obtain ⟨k', e⟩ := ke
      simp only
      split
      · obtain ⟨h1, h2⟩ := insertEntry_replays (hinv k' e hc)
        simp [h1, h2]
      · exact hfwd _ _

/-- **F8, CD isolation.** After any sequence of earlier queries (any
opcode, any header bits), a CD = 0 standard query with a question gets
exactly the upstream's CD = 0 answer. -/
theorem cd_isolation (upstream : Bool → Packet) (earlier : List Packet) (q : Packet)
    (hop : q.header.opcode = 0) (hcd : q.header.cd = false) (hq : (cacheKey q).isSome) :
    (handle (earlier.foldl (fun c p => (handle c upstream p).2) none) upstream q).1
      = ((upstream false).header.rcode, (upstream false).answers) :=
  cd0_answer upstream _ q (foldl_FromCd0 upstream earlier none (fun _ _ h => by simp at h))
    hop hcd hq

/-- The former counterexample: after a CD = 1 query, a CD = 0 client still
gets the validating upstream's SERVFAIL. -/
theorem cd_isolation_validating : CdIsolation := by
  intro earlier
  have := cd_isolation validatingUpstream (earlier.map query) (query false) (by decide)
    (by decide) (by decide)
  simp only [List.foldl_map] at this
  simp only [this]
  decide

/-- Lookups ignore case (C6): `Www.Example.com` finds `www.example.com`. -/
example : (({ name := #[3, 87, 119, 119, 0], tp := 1, cls := 1 } : Question).same
    { name := #[3, 119, 119, 119, 0], tp := 1, cls := 1 }) = true := by decide +kernel

/-! ## Opcode -/

/-- **F10, RFC 1035 §4.1.1**: a server returns NOTIMP ("the name server does
not support the requested kind of query") for opcodes it doesn't
implement. rdns implements only QUERY (0). -/
def OtherOpcodesNotImp : Prop :=
  ∀ (cache : Option ((Question × Bool) × Entry)) (upstream : Bool → Packet) (q : Packet),
    q.header.opcode ≠ 0 → (handle cache upstream q).1 = (RCODE_NOTIMP, #[])
      ∧ (handle cache upstream q).2 = cache

/-- Every non-QUERY message gets NOTIMP with no records and leaves the cache
alone, whatever is cached. Until #22 an UPDATE for a cached name got the
cached answer. -/
theorem other_opcodes_notimp : OtherOpcodesNotImp := by
  intro cache upstream q h
  simp [handle, h]

/-! ## DO isolation (#19) -/

/-- **F9.** An entry stored for a query with one DO bit never answers a
query with the other: the query is forwarded instead. -/
theorem do_isolation (k : Question × Bool) (e : Entry) (upstream : Bool → Packet) (q : Packet)
    (kq : Question) (hop : q.header.opcode = 0) (hk : cacheKey q = some (kq, !k.2)) :
    handle (some (k, e)) upstream q = handle.forward (some (k, e)) upstream q (kq, !k.2) := by
  unfold handle
  simp only [hop, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hk]
  simp [keySame]

end Rdns
