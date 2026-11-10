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

/-- `filter_map(|mut a| { a.ttl = a.ttl.min(a.soa_minimum()?); Some(a) })`:
keep SOAs, with their TTL capped at MINIMUM (#20). -/
def capSoa (a : Answer) : Option Answer := a.soaMinimum.map (fun m => { a with ttl := min a.ttl m })

/-- `DNSCache::insert_at` with `min_ttl`: the entry stored, if any. -/
def insertEntry (minTtl : UInt32) (r : Packet) : Option Entry :=
  match cacheTtl r with
  | none => none
  | some ttl =>
    let negative := r.answers.isEmpty
    let authorities := if negative then r.authorities.filterMap capSoa else #[]
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

theorem soaMinimum_with_ttl (a : Answer) (x : UInt32) :
    ({ a with ttl := x } : Answer).soaMinimum = a.soaMinimum := rfl

/-- A record that is just a TTL: `servedTtl` looks at nothing else. -/
def ttlOnly (x : UInt32) : Answer := { (default : Answer) with ttl := x }

theorem ttlOnly_ttl (x : UInt32) : (ttlOnly x).ttl = x := rfl

theorem servedTtl_ttl (a : Answer) (t : Nat) : servedTtl a t = servedTtl (ttlOnly a.ttl) t := rfl

/-- The first SOA a downstream resolver sees in the capped authority
section is the first SOA of the original one, with its TTL capped. -/
theorem findSome_capSoa (l : List Answer) (t : Nat) :
    (l.filterMap capSoa).findSome? (fun a => a.soaMinimum.map (fun m => (servedTtl a t, m)))
      = (l.findSome? (fun a => a.soaMinimum.map (fun m => (a.ttl, m)))).map
          (fun p => (servedTtl (ttlOnly (min p.1 p.2)) t, p.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hm : a.soaMinimum with
    | none =>
      have hc : capSoa a = none := by simp [capSoa, hm]
      rw [List.filterMap_cons_none hc, ih, List.findSome?_cons_of_isNone (by simp [hm])]
    | some m =>
      have hc : capSoa a = some { a with ttl := min a.ttl m } := by simp [capSoa, hm]
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
          split at hm
          · next hneg =>
            simp only [downstreamNegTtl, ← Array.findSome?_toList, Array.toList_filterMap,
              findSome_capSoa] at hm
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
          · simp [downstreamNegTtl] at hm
      · rfl
    · rfl
  · rfl

/-- The former counterexample, now honest. -/
example : negHonestAt 0 (resp RCODE_NXDOMAIN #[] #[soa 3600 300]) 299500000000 = true := by
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
