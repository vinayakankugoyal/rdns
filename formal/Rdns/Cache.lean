import Rdns.Packet

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

/-- `negative_ttl`: `min(SOA TTL, MINIMUM)` of the first SOA. -/
def negativeTtl (auth : Array Answer) : Option UInt32 :=
  auth.findSome? (fun a => a.soaMinimum.map (fun m => min a.ttl m))

/-- `a.into_iter().chain(b).min()`. -/
def minOpt : Option UInt32 → Option UInt32 → Option UInt32
  | none, none => none
  | some x, none => some x
  | none, some y => some y
  | some x, some y => some (min x y)

/-- `cache_ttl`. -/
def cacheTtl (r : Packet) : Option UInt32 :=
  if r.header.tc = 1 then none
  else
    let answers := minTtl? r.answers
    let negative := negativeTtl r.authorities
    let ttl? : Option UInt32 :=
      if r.header.rcode = RCODE_NOERROR then minOpt answers negative
      else if r.header.rcode = RCODE_NXDOMAIN then
        negative.map (fun n => min n (answers.getD 0xFFFFFFFF))
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
    let authorities := r.authorities.filter (·.soaMinimum.isSome)
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

/-- **Records never outlive their TTL downstream** (the TTL arithmetic).
If rdns serves record `a` at time `t` with the TTL `response_bytes`
writes for age `ageAt t` (which is what `handle_dns_request` passes, as
`hit.age`), a downstream cache drops it at `t + s` seconds, no later than
the record's own expiry (or `t` itself, if the record has already expired
and is served with TTL 0). This is a statement about `satSub` and the
rounding in `ageAt`, independent of `min_ttl`; that `main.rs` passes
`hit.age` is not modelled. -/
theorem served_record_never_outlives_ttl (a : Answer) (t : Nat) (h : ageAt t < 2 ^ 32) :
    t + servedTtl a t * NS ≤ max t (a.ttl.toNat * NS) := by
  rw [servedTtl_eq a t h]
  have h1 := ageAt_ge t
  by_cases hc : a.ttl.toNat ≤ ageAt t
  · simp [Nat.sub_eq_zero_of_le hc]; omega
  · have : (a.ttl.toNat - ageAt t) * NS = a.ttl.toNat * NS - ageAt t * NS := Nat.sub_mul _ _ _
    omega

theorem u32_min_le_left (a b : UInt32) : min a b ≤ a := by
  rw [UInt32.min_def]; split
  · exact UInt32.le_iff_toNat_le.mpr (Nat.le_refl _)
  · next h => rw [UInt32.le_iff_toNat_le] at h ⊢; omega
theorem u32_min_le_right (a b : UInt32) : min a b ≤ b := by
  rw [UInt32.min_def]; split
  · assumption
  · exact UInt32.le_iff_toNat_le.mpr (Nat.le_refl _)
theorem u32_le_trans {a b c : UInt32} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rw [UInt32.le_iff_toNat_le] at *; omega
theorem u32_max_zero (a : UInt32) : max a 0 = a := by
  rw [UInt32.max_def]; split
  · next h =>
    rw [UInt32.le_iff_toNat_le] at h
    exact UInt32.toNat_inj.mp (by simp at h ⊢; omega)
  · rfl

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

theorem foldl_min_some (l : List Answer) (x : UInt32) :
    (l.foldl (fun acc a => some (match acc with | none => a.ttl | some m => min m a.ttl))
      (some x)).isSome := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => exact ih _

/-- `min()` of a non-empty iterator is `Some`. -/
theorem minTtl?_none (as : Array Answer) (h : minTtl? as = none) : ∀ a ∈ as, False := by
  intro a ha
  unfold minTtl? at h
  rw [← Array.foldl_toList] at h
  have hmem := Array.mem_toList_iff.mpr ha
  cases hl : as.toList with
  | nil => simp [hl] at hmem
  | cons b l =>
    rw [hl] at h
    have := foldl_min_some l b.ttl
    simp only [List.foldl_cons] at h
    rw [h] at this; simp at this

theorem minOpt_le {a b : Option UInt32} {t : UInt32} (h : minOpt a b = some t) :
    (∀ x, a = some x → t ≤ x) ∧ (∀ y, b = some y → t ≤ y) := by
  have refl : ∀ x : UInt32, x ≤ x := fun x => UInt32.le_iff_toNat_le.mpr (Nat.le_refl _)
  cases a with
  | none => cases b with
    | none => simp [minOpt] at h
    | some y =>
      simp only [minOpt, Option.some.injEq] at h; subst h
      exact ⟨fun _ hx => by simp at hx, fun _ hy => by cases hy; exact refl _⟩
  | some x => cases b with
    | none =>
      simp only [minOpt, Option.some.injEq] at h; subst h
      exact ⟨fun _ hx => by cases hx; exact refl _, fun _ hy => by simp at hy⟩
    | some y =>
      simp only [minOpt, Option.some.injEq] at h; subst h
      exact ⟨fun _ hx => by cases hx; exact u32_min_le_left _ _,
             fun _ hy => by cases hy; exact u32_min_le_right _ _⟩

/-- **The lifetime is a lower bound.** Whatever `cache_ttl` returns is at
most every answer's TTL and at most the negative TTL. -/
theorem cacheTtl_le (r : Packet) (t : UInt32) (h : cacheTtl r = some t) :
    (∀ a ∈ r.answers, t ≤ a.ttl) ∧ (∀ n, negativeTtl r.authorities = some n → t ≤ n) := by
  unfold cacheTtl at h
  split at h
  · simp at h
  · -- strip the `t > 0` test
    have key : ∀ ttl? : Option UInt32, (match ttl? with
        | some t => if t > 0 then some t else none | none => none) = some t → ttl? = some t := by
      intro o ho; cases o with
      | none => simp at ho
      | some x => simp only at ho; split at ho <;> simp_all
    have h := key _ h
    have hans : ∀ m, minTtl? r.answers = some m → ∀ a ∈ r.answers, m ≤ a.ttl :=
      fun m hm => minTtl?_le r.answers m hm
    split at h
    · obtain ⟨h1, h2⟩ := minOpt_le h
      refine ⟨fun a ha => ?_, h2⟩
      cases hm : minTtl? r.answers with
      | none => exact (minTtl?_none _ hm a ha).elim
      | some m => exact u32_le_trans (h1 m hm) (hans m hm a ha)
    · split at h
      · cases hn : negativeTtl r.authorities with
        | none => simp [hn] at h
        | some n =>
          simp only [hn, Option.map_some, Option.some.injEq] at h
          subst h
          refine ⟨fun a ha => ?_, fun n' hn' => ?_⟩
          · cases hm : minTtl? r.answers with
            | none => exact (minTtl?_none _ hm a ha).elim
            | some m =>
              simp only [hm, Option.getD_some]
              exact u32_le_trans (u32_min_le_right _ _) (hans m hm a ha)
          · cases hn'; exact u32_min_le_left _ _
      · simp at h

theorem insertEntry_lifetime {r : Packet} {e : Entry} (h : insertEntry 0 r = some e) :
    ∃ t, cacheTtl r = some t ∧ e.lifetime = t.toNat := by
  unfold insertEntry at h
  split at h
  · simp at h
  · next t ht =>
    simp only [Option.some.injEq] at h; subst h
    exact ⟨t, ht, by rw [u32_max_zero]⟩

/-- **C7, no stale records.** Without `--min-cache-ttl`, no record is
served after its TTL has run out, for every response rdns caches. -/
theorem entries_never_stale (r : Packet) (e : Entry) (t : Nat)
    (hins : insertEntry 0 r = some e) (hlive : e.live t) :
    ∀ a ∈ e.response.answers, t < a.ttl.toNat * NS := by
  obtain ⟨ttl, hc, hl⟩ := insertEntry_lifetime hins
  have hans : e.response.answers = r.answers := by
    unfold insertEntry at hins; rw [hc] at hins; simp only [Option.some.injEq] at hins
    rw [← hins]
  intro a ha
  rw [hans] at ha
  have := UInt32.le_iff_toNat_le.mp ((cacheTtl_le r ttl hc).1 a ha)
  simp only [Entry.live, hl] at hlive
  have := Nat.mul_le_mul_right NS this
  omega

/-- The NOERROR case, as it was proved before #18. -/
theorem positive_entries_never_stale (r : Packet) (e : Entry) (t : Nat)
    (hins : insertEntry 0 r = some e) (hlive : e.live t) :
    ∀ a ∈ e.response.answers, t < a.ttl.toNat * NS :=
  entries_never_stale r e t hins hlive

/-- **C7, no stale negative answers.** Without `--min-cache-ttl`, a
response with an SOA is not served after its negative TTL has run out,
including a negative answer behind a CNAME. -/
theorem negative_entries_not_stale (r : Packet) (e : Entry) (t : Nat) (n : UInt32)
    (hins : insertEntry 0 r = some e) (hlive : e.live t)
    (hn : negativeTtl r.authorities = some n) : t < n.toNat * NS := by
  obtain ⟨ttl, hc, hl⟩ := insertEntry_lifetime hins
  have := UInt32.le_iff_toNat_le.mp ((cacheTtl_le r ttl hc).2 n hn)
  simp only [Entry.live, hl] at hlive
  have := Nat.mul_le_mul_right NS this
  omega

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

/-! ### Negative answers behind a CNAME

Until #18, `cache_ttl` bounded a negative answer behind a CNAME by only one
of its two TTLs, and `insert_at` dropped its SOA. The counterexamples were:

* NODATA behind a CNAME (TTL 3600) with negative TTL 60: "no AAAA" was
  served for an hour (`entries_never_stale`, `negative_entries_not_stale`
  above now rule this out for every response);
* NXDOMAIN behind a 30-second CNAME with negative TTL 3600: the CNAME was
  served for an hour;
* the replayed NXDOMAIN had no SOA. -/

example : (insertEntry 0 (resp RCODE_NOERROR #[cname 3600] #[soa 60 60])).map (·.lifetime)
    = some 60 := by decide +kernel

example : (insertEntry 0 (resp RCODE_NXDOMAIN #[cname 30] #[soa 3600 3600])).map (·.lifetime)
    = some 30 := by decide +kernel

/-- The SOA of a negative answer behind a CNAME is kept. -/
example : (insertEntry 0 (resp RCODE_NXDOMAIN #[cname 30] #[soa 3600 3600])).map
      (·.response.authorities.size) = some 1 := by decide +kernel

/-- `cache_ttl` as `docs/SPEC.md` §3 defines it, with `∞` as `none`:
`min(A(r), N(r))` for NOERROR, and for NXDOMAIN with an SOA. -/
def specCacheTtl (r : Packet) : Option UInt32 :=
  if r.header.tc = 1 then none
  else
    let a := minTtl? r.answers
    let n := negativeTtl r.authorities
    let ttl? : Option UInt32 :=
      if r.header.rcode = RCODE_NOERROR ∨ (r.header.rcode = RCODE_NXDOMAIN ∧ n.isSome) then
        minOpt a n
      else none
    match ttl? with
    | some t => if t > 0 then some t else none
    | none => none

theorem u32_min_comm (a b : UInt32) : min a b = min b a := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.min_def, UInt32.min_def]
  split <;> split <;> simp_all [UInt32.le_iff_toNat_le] <;> omega

theorem u32_min_max (a : UInt32) : min a 0xFFFFFFFF = a := by
  rw [UInt32.min_def]; split
  · rfl
  · next h => exact absurd (UInt32.le_iff_toNat_le.mpr (by have := a.toNat_lt; simp; omega)) h

/-- **C4** (apart from the top-bit clause, #21): `cache_ttl` is the spec's
definition, for every response. The former counterexample, NXDOMAIN
behind a CNAME, is one instance. -/
theorem cacheTtl_eq_spec (r : Packet) : cacheTtl r = specCacheTtl r := by
  unfold cacheTtl specCacheTtl
  split
  · rfl
  · congr 1
    by_cases h1 : r.header.rcode = RCODE_NOERROR
    · simp [h1]
    · by_cases h2 : r.header.rcode = RCODE_NXDOMAIN
      · simp only [h1, h2, ↓reduceIte, true_and, false_or]
        cases negativeTtl r.authorities with
        | none => rfl
        | some n =>
          cases minTtl? r.answers with
          | none => simp [minOpt, u32_min_max]
          | some m => simp [minOpt, u32_min_comm]
      · simp [h1, h2]

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


/-! ### DNSSEC records in negative answers -/

def nsec : Answer := { name := nm, tp := 47, cls := 1, ttl := 300, data := #[0, 0, 6, 0, 0, 0, 3] }
def rrsig : Answer := { name := nm, tp := 46, cls := 1, ttl := 300, data := #[0, 6, 13, 2] }

/-- **RFC 2308 §5**: "The NXT record, if it exists in the authority section
of a negative answer received, MUST be stored such that it can be be
located and returned with SOA record in the authority section, as should
any SIG records in the authority section." (NSEC and RRSIG today.) -/
def keepsProofsAt (r : Packet) : Bool :=
  match insertEntry 0 r with
  | some e => e.response.authorities.size == r.authorities.size
  | none => true

def NegativeEntriesKeepProofs : Prop :=
  ∀ r : Packet, r.answers.isEmpty = true → keepsProofsAt r = true

/-- **Counterexample.** `insert_at` keeps only the SOA, so a signed NXDOMAIN
(SOA, NSEC, RRSIG) is replayed without its proof of non-existence, and a
validating stub behind rdns can't validate the cached answer. -/
theorem bug_negative_entries_drop_nsec : ¬ NegativeEntriesKeepProofs := fun h =>
  absurd (h (resp RCODE_NXDOMAIN #[] #[soa 3600 300, nsec, rrsig]) (by decide +kernel))
    (by decide +kernel)

end Rdns
