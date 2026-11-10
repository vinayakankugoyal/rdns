import Rdns.Packet
import Std.Tactic.BVDecide

/-!
# Cache (`src/cache.rs`)

Models `cache_ttl`, `DNSCache::insert_at` and `DNSCache::get_at`.

Time is a natural number of nanoseconds since the entry was inserted
(Rust's `Instant` has nanosecond resolution). An entry inserted at time 0
with lifetime `L` seconds is live at `t` iff `t < L·10⁹`
(`entry.expiration > now`), and `get_at` reports its age as
`⌈t / 10⁹⌉` seconds (`as_secs() + (subsec_nanos() > 0)`). The age saturates
at `u32::MAX`, which never matters: `L ≤ u32::MAX`.

The properties at the end are the promises rdns makes in `README.md`,
`src/cache.rs` and `docs/SPEC.md`. Some of them are *false*; for those, the
file proves the negation with a concrete counterexample instead of
weakening the statement.
-/

namespace Rdns

set_option linter.unusedVariables false

/-- `Answer::soa_minimum`. -/
def Answer.soaMinimum (a : Answer) : Option UInt32 :=
  if a.tp ≠ TYPE_SOA ∨ a.data.size < 20 then none
  else
    let n := a.data.size
    some (be32 a.data[n - 4]! a.data[n - 3]! a.data[n - 2]! a.data[n - 1]!)

/-- `answers.iter().map(|a| a.ttl).min()`. -/
def minTtl? (as : Array Answer) : Option UInt32 :=
  as.foldl (fun acc a => some (match acc with | none => a.ttl | some m => min m a.ttl)) none

/-- `cache_ttl`. -/
def cacheTtl (r : Packet) : Option UInt32 :=
  if r.header.tc = 1 then none
  else
    let ttl? : Option UInt32 :=
      if r.header.rcode = RCODE_NOERROR ∧ ¬ r.answers.isEmpty then
        minTtl? r.answers
      else if r.header.rcode = RCODE_NOERROR ∨ r.header.rcode = RCODE_NXDOMAIN then
        (r.authorities.findSome? (fun a => a.soaMinimum.map (fun m => (a.ttl, m)))).map
          (fun p => min p.1 p.2)
      else none
    match ttl? with
    | some t => if t > 0 then some t else none
    | none => none

structure CachedResponse where
  rcode : UInt8
  answers : Array Answer
  authorities : Array Answer
  deriving Repr

structure Entry where
  response : CachedResponse
  /-- Seconds from insertion to expiration. -/
  lifetime : Nat
  deriving Repr

/-- `DNSCache::insert_at` with `min_ttl`: the entry stored, if any. -/
def insertEntry (minTtl : UInt32) (r : Packet) : Option Entry :=
  match cacheTtl r with
  | none => none
  | some ttl =>
    let negative := r.answers.isEmpty
    let authorities := if negative then r.authorities.filter (·.soaMinimum.isSome) else #[]
    some { response := { rcode := r.header.rcode, answers := r.answers, authorities }
           lifetime := (max ttl minTtl).toNat }

def NS : Nat := 1000000000

def Entry.live (e : Entry) (t : Nat) : Prop := t < e.lifetime * NS

instance (e : Entry) (t : Nat) : Decidable (e.live t) := Nat.decLt t (e.lifetime * NS)

/-- `get_at`'s age: whole seconds, rounded up. -/
def ageAt (t : Nat) : Nat := (t + NS - 1) / NS

/-- The TTL `response_bytes` writes for record `a` when served at `t`. -/
def servedTtl (a : Answer) (t : Nat) : Nat := (satSub a.ttl (UInt32.ofNat (ageAt t))).toNat

/-- Every record a cache hit replays. -/
def CachedResponse.records (c : CachedResponse) : Array Answer := c.answers ++ c.authorities

/-! ## Facts about time -/

theorem ageAt_ge (t : Nat) : t ≤ ageAt t * NS := by
  unfold ageAt NS
  have := Nat.lt_mul_div_succ (t + 1000000000 - 1) (show 0 < 1000000000 by decide)
  omega

theorem ageAt_lt (t : Nat) : ageAt t * NS < t + NS := by
  unfold ageAt NS
  have := Nat.div_mul_le_self (t + 1000000000 - 1) 1000000000
  omega

theorem servedTtl_eq (a : Answer) (t : Nat) (h : ageAt t < 2 ^ 32) :
    servedTtl a t = a.ttl.toNat - ageAt t := by
  unfold servedTtl satSub
  have hof : (UInt32.ofNat (ageAt t)).toNat = ageAt t := by
    simp [UInt32.toNat_ofNat]; omega
  split
  next hle =>
    rw [UInt32.toNat_sub_of_le _ _ hle, hof]
  next hlt =>
    have : a.ttl.toNat < ageAt t := by
      rw [← hof]; exact UInt32.lt_iff_toNat_lt.mp (by simpa using hlt)
    simp; omega

/-! ## Properties that hold -/

/-- **Records never outlive their TTL downstream.** Whatever `min_ttl` is,
a record served at `t` with TTL `s` is dropped by a downstream cache at
`t + s` seconds, which is no later than the record's own expiry (or `t`
itself, if the record has already expired and is served with TTL 0). -/
theorem served_record_never_outlives_ttl (a : Answer) (t : Nat) (h : ageAt t < 2 ^ 32) :
    t + servedTtl a t * NS ≤ max t (a.ttl.toNat * NS) := by
  rw [servedTtl_eq a t h]
  have h1 := ageAt_ge t
  by_cases hc : a.ttl.toNat ≤ ageAt t
  · simp [Nat.sub_eq_zero_of_le hc]; omega
  · have : (a.ttl.toNat - ageAt t) * NS = a.ttl.toNat * NS - ageAt t * NS := Nat.sub_mul _ _ _
    omega

theorem u32_min_le_left (a b : UInt32) : min a b ≤ a := by rw [UInt32.min_def]; bv_decide
theorem u32_min_le_right (a b : UInt32) : min a b ≤ b := by rw [UInt32.min_def]; bv_decide
theorem u32_le_trans {a b c : UInt32} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by bv_decide
theorem u32_max_zero (a : UInt32) : max a 0 = a := by rw [UInt32.max_def]; bv_decide

theorem minTtl?_le (as : Array Answer) (m : UInt32) (h : minTtl? as = some m) :
    ∀ a ∈ as, m ≤ a.ttl := by
  unfold minTtl? at h
  rw [← Array.foldl_toList] at h
  suffices ∀ (l : List Answer) (init : Option UInt32),
      l.foldl (fun acc a => some (match acc with | none => a.ttl | some m => min m a.ttl)) init
        = some m →
      (∀ x, init = some x → m ≤ x) ∧ ∀ a ∈ l, m ≤ a.ttl by
    intro a ha
    exact (this as.toList none h).2 a (Array.mem_toList_iff.mpr ha)
  intro l
  induction l with
  | nil => intro init h; simp at h; subst h; simp [UInt32.le_refl]
  | cons x xs ih =>
    intro init h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    cases init with
    | none =>
      have hx : m ≤ x.ttl := h1 _ rfl
      refine ⟨by simp, ?_⟩
      intro a ha
      cases List.mem_cons.mp ha with
      | inl e => subst e; exact hx
      | inr e => exact h2 a e
    | some y =>
      have hmin : m ≤ min y x.ttl := h1 _ rfl
      have hy : min y x.ttl ≤ y := u32_min_le_left _ _
      have hx : min y x.ttl ≤ x.ttl := u32_min_le_right _ _
      refine ⟨fun z hz => ?_, ?_⟩
      · cases hz; exact u32_le_trans hmin hy
      · intro a ha
        cases List.mem_cons.mp ha with
        | inl e => subst e; exact u32_le_trans hmin hx
        | inr e => exact h2 a e

/-- **No stale positive answers.** Without `--min-cache-ttl`, a NOERROR
response with answers is never served after any of its records has
expired: the entry lives exactly as long as its shortest TTL. -/
theorem positive_entries_never_stale (r : Packet) (e : Entry) (t : Nat)
    (hpos : r.header.rcode = RCODE_NOERROR) (hne : ¬ r.answers.isEmpty)
    (hins : insertEntry 0 r = some e) (hlive : e.live t) :
    ∀ a ∈ e.response.answers, t < a.ttl.toNat * NS := by
  unfold insertEntry at hins
  split at hins
  next => simp at hins
  next ttl hc =>
    simp only [Option.some.injEq] at hins
    subst hins
    intro a ha
    unfold cacheTtl at hc
    split at hc
    next => simp at hc
    next htc =>
      simp only [hpos, hne, not_false_eq_true, and_self, ↓reduceIte] at hc
      split at hc
      next m hm =>
        split at hc
        next =>
          simp only [Option.some.injEq] at hc; subst hc
          have := minTtl?_le r.answers m hm a ha
          have hle : m.toNat ≤ a.ttl.toNat := UInt32.le_iff_toNat_le.mp this
          simp only [Entry.live] at hlive
          have : (max m 0).toNat = m.toNat := by rw [u32_max_zero]
          rw [this] at hlive
          have := Nat.mul_le_mul_right NS hle
          omega
        next => simp at hc
      next => simp at hc

/-! ## Properties that fail

Each is a guarantee as rdns states it, followed by a proof that it is
false, with the counterexample. The statement is kept as strong as rdns
claims it; it is not weakened until it becomes provable.

Each property is phrased as a Boolean check at one point (`…At`), so a
counterexample is a closed term the kernel evaluates. -/

/-- A name `\x01x\x00`, and records for building responses. -/
def nm : Bytes := #[1, 120, 0]
def aRec (ttl : UInt32) : Answer := { name := nm, tp := TYPE_A, cls := 1, ttl, data := #[1, 2, 3, 4] }
def cname (ttl : UInt32) : Answer := { name := nm, tp := 5, cls := 1, ttl, data := #[1, 121, 0] }
/-- SOA RDATA as `from_bytes` decodes it: MNAME ".", RNAME ".",
SERIAL..EXPIRE = 0, then MINIMUM. -/
def soa (ttl minimum : UInt32) : Answer :=
  { name := nm, tp := TYPE_SOA, cls := 1, ttl,
    data := #[0, 0] ++ Array.replicate 16 0 ++ toBe32 minimum }

def resp (rcode : UInt8) (ans auth : Array Answer) : Packet :=
  { header := { (default : Header) with qr := 1, rcode }
    questions := #[{ name := nm, tp := TYPE_A, cls := 1 }]
    answers := ans, authorities := auth, resources := #[] }

/-- The negative-caching TTL of a response, as RFC 2308 §5 defines it and as
a downstream resolver computes it: `min(SOA TTL, SOA MINIMUM)` of the SOA in
the authority section. -/
def negTtl (auth : Array Answer) : Option Nat :=
  (auth.findSome? (fun a => a.soaMinimum.map (fun m => (a.ttl, m)))).map
    (fun p => min p.1.toNat p.2.toNat)

/-- How long a downstream resolver negatively caches the response rdns
serves at `t`: `min(served SOA TTL, MINIMUM)`. MINIMUM is a field of the
RDATA, so rdns replays it unchanged. -/
def downstreamNegTtl (c : CachedResponse) (t : Nat) : Option Nat :=
  (c.authorities.findSome? (fun a => a.soaMinimum.map (fun m => (servedTtl a t, m)))).map
    (fun p => min p.1 p.2.toNat)

/-! ### Negative answers outlive their negative TTL downstream -/

def negHonestAt (minTtl : UInt32) (r : Packet) (t : Nat) : Bool :=
  match insertEntry minTtl r, negTtl r.authorities with
  | some e, some n =>
    if e.live t then
      match downstreamNegTtl e.response t with
      | some m => decide (t + m * NS ≤ max t (n * NS))
      | none => true
    else true
  | _, _ => true

/-- **The promise** (`README.md`; `src/cache.rs`: "downstream caches never
hold them longer than the authority allowed"), for negative answers: a
downstream resolver handed a cached negative answer at `t` stops believing
it by the time the authority's negative TTL runs out (or at `t`, if that
has already passed). -/
def NegativeAnswersHonest : Prop := ∀ minTtl r t, negHonestAt minTtl r t = true

/-- **Counterexample.** An NXDOMAIN whose SOA has TTL 3600 and MINIMUM 300:
RFC 2308 gives it a negative TTL of 300 s. rdns keeps it 300 s, but
served at t = 299.5 s the SOA says TTL 3300, MINIMUM 300, so the
downstream resolver keeps the NXDOMAIN until t = 599.5 s. -/
theorem bug_negative_ttl_extended : ¬ NegativeAnswersHonest := fun h =>
  absurd (h 0 (resp RCODE_NXDOMAIN #[] #[soa 3600 300]) 299500000000) (by decide +kernel)

/-- With `--min-cache-ttl 3600` the same answer is believed for up to
3600 + 300 s. -/
example : negHonestAt 3600 (resp RCODE_NXDOMAIN #[] #[soa 86400 300]) (3599 * NS) = false := by
  decide +kernel

/-! ### Negative answers behind a CNAME are cached on the wrong TTL -/

def negNotStaleAt (r : Packet) (t : Nat) : Bool :=
  match insertEntry 0 r, negTtl r.authorities with
  | some e, some n => if e.live t then decide (t < n * NS) else true
  | _, _ => true

/-- **No stale negative answers.** Without `--min-cache-ttl`, rdns stops
serving a negative answer (NXDOMAIN, or NOERROR/NODATA with an SOA) once
its negative TTL has run out. -/
def NegativeEntriesNotStale : Prop := ∀ r t, negNotStaleAt r t = true

/-- **Counterexample (NODATA behind a CNAME).** The AAAA query for a name
that is a CNAME (TTL 3600) to a target with no AAAA records is answered
NOERROR, with the CNAME and the target zone's SOA (negative TTL 60). rdns
takes the entry's lifetime from the CNAME alone, so it keeps answering
"no AAAA" for an hour, 60 times longer than allowed. -/
theorem bug_cname_nodata_stale : ¬ NegativeEntriesNotStale := fun h =>
  absurd (h (resp RCODE_NOERROR #[cname 3600] #[soa 60 60]) (3000 * NS)) (by decide +kernel)

def notStaleAt (r : Packet) (t : Nat) : Bool :=
  match insertEntry 0 r with
  | some e => if e.live t then e.response.answers.all (fun a => decide (t < a.ttl.toNat * NS))
              else true
  | none => true

/-- **No stale records.** Without `--min-cache-ttl`, rdns never serves a
record after its TTL has run out. `positive_entries_never_stale` proves
this for NOERROR responses; this is the same promise for all responses. -/
def EntriesNeverStale : Prop := ∀ r t, notStaleAt r t = true

/-- **Counterexample (NXDOMAIN behind a CNAME).** `www` is a CNAME
(TTL 30) to a name that doesn't exist; the target zone's SOA gives a
negative TTL of 3600. rdns takes the lifetime from the SOA alone and keeps
serving the 30-second CNAME for an hour (with TTL 0 once it has expired),
so a changed CNAME isn't seen for an hour. -/
theorem bug_cname_nxdomain_stale : ¬ EntriesNeverStale := fun h =>
  absurd (h (resp RCODE_NXDOMAIN #[cname 30] #[soa 3600 3600]) (1000 * NS)) (by decide +kernel)

/-- ...and the replayed NXDOMAIN has lost its SOA, so (RFC 2308 §5)
downstream resolvers can't cache it negatively at all. -/
theorem bug_cname_nxdomain_drops_soa :
    (insertEntry 0 (resp RCODE_NXDOMAIN #[cname 30] #[soa 3600 3600])).map
      (·.response.authorities.size) = some 0 := by decide +kernel

/-- `cache_ttl` exactly as `docs/SPEC.md` §3 defines it: the SOA branch
applies only when there are no answers. -/
def specCacheTtl (r : Packet) : Option UInt32 :=
  if r.header.tc = 1 then none
  else
    let ttl? : Option UInt32 :=
      if r.header.rcode = RCODE_NOERROR ∧ ¬ r.answers.isEmpty then minTtl? r.answers
      else if (r.header.rcode = RCODE_NOERROR ∨ r.header.rcode = RCODE_NXDOMAIN)
          ∧ r.answers.isEmpty then
        (r.authorities.findSome? (fun a => a.soaMinimum.map (fun m => (a.ttl, m)))).map
          (fun p => min p.1 p.2)
      else none
    match ttl? with
    | some t => if t > 0 then some t else none
    | none => none

/-- **C4 doesn't hold as the spec writes it**: the code caches an
NXDOMAIN-with-answers response that the spec's `cache_ttl` refuses. -/
theorem bug_c4_spec_mismatch : ¬ ∀ r, cacheTtl r = specCacheTtl r := fun h =>
  absurd (h (resp RCODE_NXDOMAIN #[cname 30] #[soa 3600 3600])) (by decide +kernel)

/-! ### TTLs with the top bit set -/

/-- **RFC 2181 §8**: "Implementations should treat TTL values received with
the most significant bit set as if the entire value received was zero."
So such a response must not be cached. -/
def HighBitTtlsNotCached : Prop :=
  ∀ r : Packet, r.answers.any (·.ttl ≥ 0x80000000) = true → cacheTtl r = none

/-- **Counterexample.** A record with TTL `0xFFFFFFFF` is cached for
2³² − 1 seconds (136 years) and served with that TTL. -/
theorem bug_high_bit_ttl_cached : ¬ HighBitTtlsNotCached := fun h =>
  absurd (h (resp RCODE_NOERROR #[aRec 0xFFFFFFFF] #[]) (by decide +kernel)) (by decide +kernel)

example : (insertEntry 0 (resp RCODE_NOERROR #[aRec 0xFFFFFFFF] #[])).map (·.lifetime)
    = some 4294967295 := by decide +kernel

/-! ### C3, as stated in the spec -/

def c3At (minTtl : UInt32) (r : Packet) (t : Nat) : Bool :=
  match insertEntry minTtl r with
  | some e => if e.live t then
      e.response.records.all (fun a => decide (servedTtl a t * NS ≤ e.lifetime * NS - t))
    else true
  | none => true

/-- **C3 as written in `docs/SPEC.md`**: "at any time `t` the entry is live,
every served TTL ≤ its remaining lifetime". -/
def C3 : Prop := ∀ minTtl r t, c3At minTtl r t = true

/-- **Counterexample.** Records with TTLs 60 and 3600 (say an A record and
the CNAME in front of it): the entry lives 60 s but serves the CNAME with
TTL 3600. The C3 test only ever inserts a single record. This one is
harmless, because the CNAME really may be cached for 3600 s
(`served_record_never_outlives_ttl`); it is the spec that overclaims. -/
theorem c3_as_stated_is_false : ¬ C3 := fun h =>
  absurd (h 0 (resp RCODE_NOERROR #[aRec 60, cname 3600] #[]) 0) (by decide +kernel)

end Rdns
