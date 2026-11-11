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

/-- `received_ttl`: a TTL with the top bit set counts as 0 (RFC 2181 §8). -/
def receivedTtl (t : UInt32) : UInt32 := if t ≥ 0x80000000 then 0 else t

/-- A record with its TTL as received. -/
def Answer.received (a : Answer) : Answer := { a with ttl := receivedTtl a.ttl }

/-- `negative_ttl`: `min(SOA TTL, MINIMUM)` of the first SOA, both as
received TTLs. -/
def negativeTtl (auth : Array Answer) : Option UInt32 :=
  auth.findSome? (fun a => a.soaMinimum.map (fun m => min (receivedTtl a.ttl) (receivedTtl m)))

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
    let answers := minTtl? (r.answers.map Answer.received)
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

/-- The authority records that prove a non-existence (RFC 2308 §5). -/
def isDnssecProof (a : Answer) : Bool :=
  a.tp == TYPE_NSEC || a.tp == TYPE_NSEC3 || a.tp == TYPE_RRSIG

/-- The `filter_map` closure of `insert_at`: every SOA is kept with its TTL
capped at MINIMUM (#18, #20); NSEC, NSEC3 and RRSIG records are kept when
the response has an SOA, i.e. is (partly) negative (#19); nothing else. -/
def keepAuthority (negative : Bool) (a : Answer) : Option Answer :=
  match a.soaMinimum with
  | some m => some { a with ttl := min a.ttl m }
  | none => if negative && isDnssecProof a then some a else none

/-- `DNSCache::insert_at` with `min_ttl`: the entry stored, if any. -/
def insertEntry (minTtl : UInt32) (r : Packet) : Option Entry :=
  match cacheTtl r with
  | none => none
  | some ttl =>
    let negative := r.authorities.any (·.soaMinimum.isSome)
    let authorities := r.authorities.filterMap (keepAuthority negative)
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

theorem receivedTtl_le (t : UInt32) : receivedTtl t ≤ t := by
  unfold receivedTtl; split
  · exact UInt32.le_iff_toNat_le.mpr (by simp)
  · exact UInt32.le_iff_toNat_le.mpr (Nat.le_refl _)

theorem receivedTtl_lt (t : UInt32) : receivedTtl t < 0x80000000 := by
  unfold receivedTtl; split
  · decide
  · next h =>
    have h' : ¬ (0x80000000 : UInt32).toNat ≤ t.toNat := fun h' => h (UInt32.le_iff_toNat_le.mpr h')
    rw [UInt32.lt_iff_toNat_lt]; simp at h' ⊢; omega

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
    (∀ a ∈ r.answers, t ≤ receivedTtl a.ttl) ∧ (∀ n, negativeTtl r.authorities = some n → t ≤ n) := by
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
    have hans : ∀ m, minTtl? (r.answers.map Answer.received) = some m →
        ∀ a ∈ r.answers, m ≤ receivedTtl a.ttl := fun m hm a ha =>
      minTtl?_le _ m hm a.received (Array.mem_map_of_mem ha)
    have hnone : minTtl? (r.answers.map Answer.received) = none → ∀ a ∈ r.answers, False :=
      fun hm a ha => minTtl?_none _ hm a.received (Array.mem_map_of_mem ha)
    split at h
    · obtain ⟨h1, h2⟩ := minOpt_le h
      refine ⟨fun a ha => ?_, h2⟩
      cases hm : minTtl? (r.answers.map Answer.received) with
      | none => exact (hnone hm a ha).elim
      | some m => exact u32_le_trans (h1 m hm) (hans m hm a ha)
    · split at h
      · cases hn : negativeTtl r.authorities with
        | none => simp [hn] at h
        | some n =>
          simp only [hn, Option.map_some, Option.some.injEq] at h
          subst h
          refine ⟨fun a ha => ?_, fun n' hn' => ?_⟩
          · cases hm : minTtl? (r.answers.map Answer.received) with
            | none => exact (hnone hm a ha).elim
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
  have := UInt32.le_iff_toNat_le.mp
    (u32_le_trans ((cacheTtl_le r ttl hc).1 a ha) (receivedTtl_le a.ttl))
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

theorem soaMinimum_with_ttl (a : Answer) (x : UInt32) :
    ({ a with ttl := x } : Answer).soaMinimum = a.soaMinimum := rfl

/-- A record that is just a TTL: `servedTtl` looks at nothing else. -/
def ttlOnly (x : UInt32) : Answer := { (default : Answer) with ttl := x }

theorem ttlOnly_ttl (x : UInt32) : (ttlOnly x).ttl = x := rfl

theorem servedTtl_ttl (a : Answer) (t : Nat) : servedTtl a t = servedTtl (ttlOnly a.ttl) t := rfl

/-- The first SOA a downstream resolver sees in the stored authority
section is the first SOA of the original one, with its TTL capped (the
NSEC/NSEC3/RRSIG records kept beside it have no MINIMUM). -/
theorem findSome_keep (neg : Bool) (l : List Answer) (t : Nat) :
    (l.filterMap (keepAuthority neg)).findSome?
        (fun a => a.soaMinimum.map (fun m => (servedTtl a t, m)))
      = (l.findSome? (fun a => a.soaMinimum.map (fun m => (a.ttl, m)))).map
          (fun p => (servedTtl (ttlOnly (min p.1 p.2)) t, p.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hm : a.soaMinimum with
    | none =>
      rw [List.findSome?_cons_of_isNone (by simp [hm])]
      cases hc : keepAuthority neg a with
      | none => rw [List.filterMap_cons_none hc, ih]
      | some a' =>
        have ha' : a' = a := by
          simp only [keepAuthority, hm] at hc; split at hc <;> simp_all
        subst ha'
        rw [List.filterMap_cons_some hc, List.findSome?_cons_of_isNone (by simp [hm]), ih]
    | some m =>
      have hc : keepAuthority neg a = some { a with ttl := min a.ttl m } := by
        simp [keepAuthority, hm]
      have hs : ({ a with ttl := min a.ttl m } : Answer).soaMinimum = some m := by
        rw [soaMinimum_with_ttl, hm]
      rw [List.filterMap_cons_some hc, List.findSome?_cons_of_isSome (by rw [hs]; rfl),
        List.findSome?_cons_of_isSome (by rw [hm]; rfl)]
      simp only [hs, hm, Option.map_some]
      rw [servedTtl_ttl]

theorem live_age (e : Entry) (t : Nat) (hl : e.lifetime < 2 ^ 32) (h : e.live t) :
    ageAt t < 2 ^ 32 := by
  have := ageAt_lt t
  simp only [Entry.live] at h
  have : ageAt t * NS < 2 ^ 32 * NS := by
    have := Nat.mul_le_mul_right NS (Nat.succ_le_of_lt hl); unfold NS at *; omega
  exact Nat.lt_of_mul_lt_mul_right this

/-- **C8, honest negative TTLs.** Whatever `min_ttl` is, a downstream
resolver handed a cached negative answer at `t` stops believing it by the
time the authority's negative TTL runs out (or at `t`, if that has already
passed). This was false until #20 (`t = 299.5 s`, SOA TTL 3600, MINIMUM
300: held until 599.5 s). -/
theorem negative_answers_honest : NegativeAnswersHonest := by
  intro minTtl r t
  unfold negHonestAt
  split
  · next e n hins hn =>
    split
    · next hlive =>
      split
      · next m hm =>
        unfold insertEntry at hins
        split at hins
        · simp at hins
        · next ttl _ =>
          simp only [Option.some.injEq] at hins
          subst hins
          have hlt : (max ttl minTtl).toNat < 2 ^ 32 := (max ttl minTtl).toNat_lt
          have hage := live_age _ t hlt hlive
          simp only [downstreamNegTtl, ← Array.findSome?_toList, Array.toList_filterMap,
            findSome_keep] at hm
          simp only [negTtl, ← Array.findSome?_toList] at hn
          cases hf : r.authorities.toList.findSome?
              (fun a => a.soaMinimum.map (fun m => (a.ttl, m))) with
          | none => simp [hf] at hn
          | some p =>
            simp only [hf, Option.map_some, Option.some.injEq] at hm hn
            subst hm hn
            have key := served_record_never_outlives_ttl (ttlOnly (min p.1 p.2)) t hage
            have hmin : (min p.1 p.2).toNat = min p.1.toNat p.2.toNat := by
              rw [UInt32.min_def]; split <;> simp_all [UInt32.le_iff_toNat_le] <;> omega
            rw [ttlOnly_ttl, hmin] at key
            have : min (servedTtl (ttlOnly (min p.1 p.2)) t) p.2.toNat
                * NS ≤ servedTtl (ttlOnly (min p.1 p.2)) t * NS :=
              Nat.mul_le_mul_right NS (Nat.min_le_left _ _)
            simp only [decide_eq_true_eq]
            omega
      · rfl
    · rfl
  · rfl

/-- The former counterexample, now honest. -/
example : negHonestAt 0 (resp RCODE_NXDOMAIN #[] #[soa 3600 300]) 299500000000 = true := by
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
    -- A TTL with the top bit set counts as 0 (`receivedTtl`; `negativeTtl`
    -- applies it to the SOA's TTL and MINIMUM).
    let a := minTtl? (r.answers.map Answer.received)
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

/-- **C4**: `cache_ttl` is the spec's definition, for every response,
including the top-bit clause. The former counterexamples, NXDOMAIN behind
a CNAME (#18) and TTL `0xFFFFFFFF` (#21), are instances. -/
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
          cases minTtl? (r.answers.map Answer.received) with
          | none => simp [minOpt, u32_min_max]
          | some m => simp [minOpt, u32_min_comm]
      · simp [h1, h2]

/-! ### TTLs with the top bit set

RFC 2181 §8: "Implementations should treat TTL values received with the
most significant bit set as if the entire value received was zero." Until
#21 a record with TTL `0xFFFFFFFF` was cached for 2³² − 1 seconds. -/

theorem minTtl?_lt (as : Array Answer) (m B : UInt32) (h : minTtl? as = some m)
    (hb : ∀ a ∈ as, a.ttl < B) : m < B := by
  by_cases hs : as.size = 0
  · have : as = #[] := Array.eq_empty_of_size_eq_zero hs
    subst this; simp [minTtl?] at h
  · have hmem : as[0]'(by omega) ∈ as := Array.getElem_mem (by omega)
    have h1 := minTtl?_le as m h _ hmem
    have h2 := hb _ hmem
    rw [UInt32.le_iff_toNat_le] at h1; rw [UInt32.lt_iff_toNat_lt] at h2 ⊢; omega

/-- **No entry outlives 2³¹ − 1 seconds** (without `--min-cache-ttl`):
`cache_ttl` never returns a TTL with the top bit set. -/
theorem gate_pos (o : Option UInt32) (t : UInt32)
    (h : (match o with | some t => if t > 0 then some t else none | none => none) = some t) :
    0 < t := by
  cases o with
  | none => simp at h
  | some x => simp only at h; split at h <;> simp_all

theorem cacheTtl_pos (r : Packet) (t : UInt32) (h : cacheTtl r = some t) : 0 < t := by
  unfold cacheTtl at h
  split at h
  · simp at h
  · exact gate_pos _ t h

theorem negativeTtl_lt (auth : Array Answer) (n : UInt32) (h : negativeTtl auth = some n) :
    n < 0x80000000 := by
  obtain ⟨a, -, ha⟩ := Array.exists_of_findSome?_eq_some h
  cases hm : a.soaMinimum with
  | none => simp [hm] at ha
  | some m =>
    simp only [hm, Option.map_some, Option.some.injEq] at ha
    subst ha
    have := receivedTtl_lt a.ttl
    have := u32_min_le_left (receivedTtl a.ttl) (receivedTtl m)
    rw [UInt32.le_iff_toNat_le] at *; rw [UInt32.lt_iff_toNat_lt] at *; omega

/-- **No entry outlives 2³¹ − 1 seconds** (without `--min-cache-ttl`):
`cache_ttl` never returns a TTL with the top bit set. -/
theorem cacheTtl_lt (r : Packet) (t : UInt32) (h : cacheTtl r = some t) : t < 0x80000000 := by
  obtain ⟨hans, hneg⟩ := cacheTtl_le r t h
  cases hn : negativeTtl r.authorities with
  | some n =>
    have h1 := hneg n hn
    have h2 := negativeTtl_lt _ n hn
    rw [UInt32.le_iff_toNat_le] at h1; rw [UInt32.lt_iff_toNat_lt] at *; omega
  | none =>
    -- no SOA: the lifetime is the minimum of the answers, so there is one
    by_cases hs : r.answers.size = 0
    · exfalso
      have he : r.answers = #[] := Array.eq_empty_of_size_eq_zero hs
      have : cacheTtl r = none := by
        unfold cacheTtl; simp [he, hn, minTtl?, minOpt]
      rw [this] at h; simp at h
    · have hmem : r.answers[0]'(by omega) ∈ r.answers := Array.getElem_mem (by omega)
      have h1 := hans _ hmem
      have h2 := receivedTtl_lt (r.answers[0]'(by omega)).ttl
      rw [UInt32.le_iff_toNat_le] at h1; rw [UInt32.lt_iff_toNat_lt] at *; omega

/-- **RFC 2181 §8**: a response with any answer TTL ≥ 2³¹ isn't cached,
whatever its RCODE (including NXDOMAIN behind a CNAME, since #18 made the
answers bound its lifetime). -/
theorem high_bit_ttls_not_cached (r : Packet) (a : Answer) (ha : a ∈ r.answers)
    (hhi : a.ttl ≥ 0x80000000) : cacheTtl r = none := by
  cases hc : cacheTtl r with
  | none => rfl
  | some t =>
    have h1 := (cacheTtl_le r t hc).1 a ha
    have h0 : receivedTtl a.ttl = 0 := by simp [receivedTtl, hhi]
    rw [h0, UInt32.le_iff_toNat_le] at h1
    have := cacheTtl_pos r t hc
    rw [UInt32.lt_iff_toNat_lt] at this
    simp at h1 this; omega

/-- The former counterexample: TTL `0xFFFFFFFF` is no longer cached. -/
example : insertEntry 0 (resp RCODE_NOERROR #[aRec 0xFFFFFFFF] #[]) |>.isNone := by decide +kernel

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

/-- **C5, DNSSEC part (RFC 2308 §5)**: "The NXT record, if it exists in the
authority section of a negative answer received, MUST be stored such that
it can be be located and returned with SOA record in the authority
section, as should any SIG records in the authority section." (NSEC,
NSEC3 and RRSIG today.) Every such record of a cached negative answer is
replayed. Until #19 only the SOA was. -/
theorem isDnssecProof_no_minimum (a : Answer) (h : isDnssecProof a = true) :
    a.soaMinimum = none := by
  have : a.tp ≠ TYPE_SOA := by
    intro he; simp [isDnssecProof, he, TYPE_SOA, TYPE_NSEC, TYPE_NSEC3, TYPE_RRSIG] at h
  simp [Answer.soaMinimum, this]

theorem negative_entries_keep_proofs (minTtl : UInt32) (r : Packet) (e : Entry)
    (hneg : r.authorities.any (·.soaMinimum.isSome) = true)
    (hins : insertEntry minTtl r = some e) :
    ∀ a ∈ r.authorities, isDnssecProof a = true → a ∈ e.response.authorities := by
  unfold insertEntry at hins
  split at hins
  · simp at hins
  · simp only [Option.some.injEq] at hins
    subst hins
    intro a ha hk
    refine Array.mem_filterMap.mpr ⟨a, ha, ?_⟩
    simp [keepAuthority, isDnssecProof_no_minimum a hk, hneg, hk]

/-- ...and the SOA with it, its TTL capped at MINIMUM (#20). -/
theorem negative_entries_keep_soa (minTtl : UInt32) (r : Packet) (e : Entry)
    (hins : insertEntry minTtl r = some e) (a : Answer) (ha : a ∈ r.authorities)
    (m : UInt32) (hm : a.soaMinimum = some m) :
    { a with ttl := min a.ttl m } ∈ e.response.authorities := by
  unfold insertEntry at hins
  split at hins
  · simp at hins
  · simp only [Option.some.injEq] at hins
    subst hins
    exact Array.mem_filterMap.mpr ⟨a, ha, by simp [keepAuthority, hm]⟩

/-- The former counterexample: a signed NXDOMAIN keeps SOA, NSEC and RRSIG. -/
example : (insertEntry 0 (resp RCODE_NXDOMAIN #[] #[soa 3600 300, nsec, rrsig])).map
    (·.response.authorities.size) = some 3 := by decide +kernel

end Rdns
