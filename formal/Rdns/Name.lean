import Rdns.Wire

/-!
# Name decoding (`src/packet.rs`, `read_name`)

`readName` follows the Rust loop statement by statement. Rust's `usize`
arithmetic is modelled with `Nat`: every addition in `read_name` is of an
in-bounds index and a value below 2¹⁶, so it cannot overflow, and the one
subtraction (`pos + 2 - start`, `pos - start`) is shown below never to
underflow, so Rust never panics where the model truncates.

The model is a *total* Lean function: Lean only accepts the definition
together with a proof that the recursion terminates. That proof is P1 (the
parser terminates on every input), checked by the kernel rather than
argued in a comment.
-/

namespace Rdns

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def MAX_NAME_LEN : Nat := 255

/-- One iteration of `read_name`'s `loop`, with the loop state
(`name`, `pos`, `used`) as arguments. -/
def readNameLoop (buf : Bytes) (start : Nat) (name : Bytes) (pos : Nat)
    (used : Option Nat) : Option (Bytes × Nat) :=
  match buf[pos]? with                                   -- let b = *buf.get(pos)?;
  | none => none
  | some b =>
    if b &&& 0xC0 = 0xC0 then                            -- 0xC0 =>
      match buf[pos + 1]? with                           --   let low = *buf.get(pos + 1)?;
      | none => none
      | some low =>
        let target := ((b.toNat &&& 0x3F) <<< 8) ||| low.toNat
        if h : target ≥ pos then none                    --   if target >= pos { return None }
        else
          -- used.get_or_insert_with(|| pos + 2 - start); pos = target;
          readNameLoop buf start name target (some (used.getD (pos + 2 - start)))
    else if b &&& 0xC0 = 0 then                          -- 0x00 =>
      -- let label = buf.get(pos..pos + 1 + b as usize)?;
      if hb : pos + 1 + b.toNat > buf.size then none
      else
        let label := buf.extract pos (pos + 1 + b.toNat)
        if hl : name.size + label.size > MAX_NAME_LEN then none
        else
          let name' := name ++ label                     -- name.extend_from_slice(label);
          let pos' := pos + label.size                   -- pos += label.len();
          if hz : b = 0 then
            some (name', used.getD (pos' - start))       -- return Some((name, used.unwrap_or_else(..)))
          else
            readNameLoop buf start name' pos' used
    else none                                            -- reserved label types
termination_by (MAX_NAME_LEN + 1 - name.size, pos)
decreasing_by
  · -- pointer: `name` unchanged, `pos` strictly decreases
    exact Prod.Lex.right _ (by omega)
  · -- label: `name` grows by `1 + b ≥ 2` bytes and stays within 255
    apply Prod.Lex.left
    have hsz : label.size = 1 + b.toNat := by
      simp only [label, Array.size_extract]; omega
    have : b.toNat ≠ 0 := fun h => hz (UInt8.toNat_inj.mp (by simpa using h))
    simp only [MAX_NAME_LEN] at *
    simp only [Array.size_append]
    simp only [label] at hl hsz
    omega

/-- `read_name(buf, start)`: the decoded name and the bytes it occupies at
`start`. -/
def readName (buf : Bytes) (start : Nat) : Option (Bytes × Nat) :=
  readNameLoop buf start #[] start none

/-! ## Well-formed names -/

/-- `WF`, as a predicate on a byte list: labels of length 1–63, then the
root label. (The 255-byte bound is stated separately.) -/
inductive Labels : List UInt8 → Prop
  | root : Labels [0]
  | cons (len : UInt8) (body rest : List UInt8) :
      1 ≤ len.toNat → len.toNat ≤ 63 → body.length = len.toNat →
      Labels rest → Labels (len :: body ++ rest)

/-- A prefix of a name: zero or more complete non-root labels. -/
inductive LabelPrefix : List UInt8 → Prop
  | nil : LabelPrefix []
  | snoc (p : List UInt8) (len : UInt8) (body : List UInt8) :
      LabelPrefix p → 1 ≤ len.toNat → len.toNat ≤ 63 → body.length = len.toNat →
      LabelPrefix (p ++ len :: body)

theorem LabelPrefix.append_root {p : List UInt8} (h : LabelPrefix p) :
    Labels (p ++ [0]) := by
  suffices ∀ rest, Labels rest → Labels (p ++ rest) from this _ Labels.root
  induction h with
  | nil => intro rest h; simpa using h
  | snoc p len body _ h1 h2 h3 ih =>
    intro rest hr
    have := ih _ (Labels.cons len body rest h1 h2 h3 hr)
    simpa [List.append_assoc] using this

def WF (n : Bytes) : Prop := Labels n.toList ∧ n.size ≤ MAX_NAME_LEN

/-! ## Facts about `extract` used below -/

theorem extract_toList_head (buf : Bytes) (pos k : Nat) (b : UInt8)
    (hb : buf[pos]? = some b) (hk : pos + 1 + k ≤ buf.size) :
    (buf.extract pos (pos + 1 + k)).toList
      = b :: (buf.extract (pos + 1) (pos + 1 + k)).toList := by
  have hp : pos < buf.size := by omega
  have hbv : buf[pos] = b := by
    rw [Array.getElem?_eq_getElem hp] at hb; exact Option.some.inj hb
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_extract, List.length_cons]; omega
  · intro i h1 h2
    cases i with
    | zero => simp [Array.getElem_toList, hbv]
    | succ i =>
      simp only [Array.getElem_toList, Array.getElem_extract, List.getElem_cons_succ]
      congr 1; omega

/-! ## P1 and P2 -/


theorem len_le_63 (b : UInt8) (h : b &&& 0xC0 = 0) : b.toNat ≤ 63 := by
  have : b ≤ 63 := by bv_decide
  exact (UInt8.le_iff_toNat_le).mp this

/-- **P2 (well-formedness) and absence of underflow.** Loop invariant: the
name built so far is a sequence of complete labels, and `used` is unset
only while no pointer has been followed, in which case `pos ≥ start` (so
Rust's `pos + 2 - start` and `pos - start` never underflow). Every name
`read_name` returns is well formed and at most 255 bytes long. -/
theorem readNameLoop_sound (buf : Bytes) (start : Nat) (name : Bytes) (pos : Nat)
    (used : Option Nat) :
    LabelPrefix name.toList → (used = none → start ≤ pos) →
      ∀ out u, readNameLoop buf start name pos used = some (out, u) → WF out := by
  induction name, pos, used using readNameLoop.induct buf start with
  | case1 name pos used hb =>
    intro _ _ out u h; unfold readNameLoop at h; simp [hb] at h
  | case2 name pos used b hb hc hlow =>
    intro _ _ out u h; unfold readNameLoop at h; simp [hb, hc, hlow] at h
  | case3 name pos used b hb hc low hlow target hge =>
    intro _ _ out u h; unfold readNameLoop at h; simp only [hb, hc, hlow, ↓reduceIte] at h
    rw [dif_pos hge] at h; simp at h
  | case4 name pos used b hb hc low hlow target hlt ih =>
    intro hpre _ out u h
    unfold readNameLoop at h; simp only [hb, hc, hlow, ↓reduceIte] at h
    rw [dif_neg hlt] at h
    exact ih hpre (by simp) out u h
  | case5 name pos used b hb hc hc0 hbig =>
    intro _ _ out u h; unfold readNameLoop at h; simp [hb, hc, hc0, hbig] at h
  | case6 name pos used b hb hc hc0 hbig label hl =>
    intro _ _ out u h; unfold readNameLoop at h
    simp only [hb, hc, hc0, ↓reduceIte] at h
    rw [dif_neg hbig, dif_pos hl] at h; simp at h
  | case7 name pos used hb hc hc0 hbig label hl =>
    intro hpre _ out u h; unfold readNameLoop at h
    simp only [hb, hc, hc0, ↓reduceIte] at h
    rw [dif_neg hbig, dif_neg hl] at h
    simp only [↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hk : pos + 1 + (0 : UInt8).toNat ≤ buf.size := by omega
    have hl0 : (buf.extract pos (pos + 1 + (0 : UInt8).toNat)).toList = [0] := by
      rw [extract_toList_head buf pos _ 0 hb hk]; simp
    refine ⟨?_, ?_⟩
    · simp only [Array.toList_append, hl0]; exact hpre.append_root
    · simp only [label, MAX_NAME_LEN] at hl ⊢; simp only [Array.size_append]; omega
  | case8 name pos used b hb hc hc0 hbig label hl name' pos' hz ih =>
    intro hpre hused out u h; unfold readNameLoop at h
    simp only [hb, hc, hc0, ↓reduceIte] at h
    rw [dif_neg hbig, dif_neg hl, dif_neg hz] at h
    have hk : pos + 1 + b.toNat ≤ buf.size := by omega
    have hpre' : LabelPrefix name'.toList := by
      simp only [name', label, Array.toList_append]
      rw [extract_toList_head buf pos b.toNat b hb hk]
      refine LabelPrefix.snoc _ b _ hpre ?_ (len_le_63 b hc0) ?_
      · have : b.toNat ≠ 0 := fun h => hz (UInt8.toNat_inj.mp (by simpa using h))
        omega
      · simp; omega
    exact ih hpre' (fun hu => by have := hused hu; simp only [pos']; omega) out u h
  | case9 name pos used b hb hc hc0 =>
    intro _ _ out u h; unfold readNameLoop at h; simp [hb, hc, hc0] at h

theorem readName_wf (buf : Bytes) (start : Nat) (out : Bytes) (u : Nat)
    (h : readName buf start = some (out, u)) : WF out :=
  readNameLoop_sound buf start #[] start none LabelPrefix.nil (fun _ => Nat.le_refl _) out u h

end Rdns
