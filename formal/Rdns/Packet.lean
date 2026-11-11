import Rdns.Name

/-!
# Messages (`src/packet.rs`, `DNSPacket`, `Question`, `Answer`)

Models `DNSPacket::from_bytes`, `read_record`, `response_bytes`,
`truncated_bytes`, `udp_payload_limit` and `set_id`, statement by
statement. The `Reader` cursor becomes an explicit position threaded
through `Option`.
-/

namespace Rdns

set_option linter.unusedVariables false

def TYPE_A : UInt16 := 1
def TYPE_SOA : UInt16 := 6
def TYPE_AAAA : UInt16 := 28
def TYPE_OPT : UInt16 := 41

def RCODE_NOERROR : UInt8 := 0
def RCODE_SERVFAIL : UInt8 := 2
def RCODE_NXDOMAIN : UInt8 := 3

def DEFAULT_UDP_PAYLOAD : Nat := 512
def MAX_UDP_PAYLOAD : Nat := 4096
def BLOCKED_TTL : UInt32 := 300

structure Question where
  name : Bytes
  tp : UInt16
  cls : UInt16
  deriving Repr, DecidableEq, Inhabited

structure Answer where
  name : Bytes
  tp : UInt16
  cls : UInt16
  ttl : UInt32
  data : Bytes
  deriving Repr, DecidableEq, Inhabited

structure Packet where
  header : Header
  questions : Array Question
  answers : Array Answer
  authorities : Array Answer
  resources : Array Answer
  deriving Repr, Inhabited, DecidableEq

/-! ## Reader -/

/-- `Reader::bytes`: `buf.get(pos..pos + n)`. -/
def rBytes (buf : Bytes) (pos n : Nat) : Option (Bytes × Nat) :=
  if pos + n ≤ buf.size then some (buf.extract pos (pos + n), pos + n) else none

def rU16 (buf : Bytes) (pos : Nat) : Option (UInt16 × Nat) := do
  let (b, p) ← rBytes buf pos 2
  pure (be16 b[0]! b[1]!, p)

def rU32 (buf : Bytes) (pos : Nat) : Option (UInt32 × Nat) := do
  let (b, p) ← rBytes buf pos 4
  pure (be32 b[0]! b[1]! b[2]! b[3]!, p)

/-- `Reader::name`. -/
def rName (buf : Bytes) (pos : Nat) : Option (Bytes × Nat) := do
  let (name, used) ← readName buf pos
  pure (name, pos + used)

inductive Field
  | name
  | fixed (n : Nat)

/-- `rdata_layout`. -/
def rdataLayout (tp : UInt16) : Option (List Field) :=
  match tp.toNat with
  | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 12 => some [.name]
  | 6 => some [.name, .name, .fixed 20]
  | 14 | 17 => some [.name, .name]
  | 15 | 18 | 21 => some [.fixed 2, .name]
  | 33 => some [.fixed 6, .name]
  | _ => none

/-- The `for field in layout` loop of `read_record`, including the
`if r.pos > end { return None }` check after every field. -/
def readFields (buf : Bytes) (stop : Nat) : List Field → Bytes → Nat → Option (Bytes × Nat)
  | [], data, pos => some (data, pos)
  | f :: fs, data, pos => do
    let (chunk, pos) ← match f with
      | .name => rName buf pos
      | .fixed n => rBytes buf pos n
    if pos > stop then none
    else readFields buf stop fs (data ++ chunk) pos

/-- `DNSPacket::read_record`. -/
def readRecord (buf : Bytes) (pos : Nat) : Option (Answer × Nat) := do
  let (name, pos) ← rName buf pos
  let (tp, pos) ← rU16 buf pos
  let (cls, pos) ← rU16 buf pos
  let (ttl, pos) ← rU32 buf pos
  let (length, pos) ← rU16 buf pos
  let stop := pos + length.toNat
  if stop > buf.size then none
  else
    let (data, pos) ← match rdataLayout tp with
      | none => rBytes buf pos length.toNat
      | some layout => do
        let (data, pos) ← readFields buf stop layout #[] pos
        if pos ≠ stop then none else pure (data, pos)
    pure ({ name, tp, cls, ttl, data }, pos)

def readQuestion (buf : Bytes) (pos : Nat) : Option (Question × Nat) := do
  let (name, pos) ← rName buf pos
  let (tp, pos) ← rU16 buf pos
  let (cls, pos) ← rU16 buf pos
  pure ({ name, tp, cls }, pos)

/-- `for _ in 0..count { out.push(read(&mut r)?) }`. -/
def readMany {α} (read : Nat → Option (α × Nat)) : Nat → Array α → Nat → Option (Array α × Nat)
  | 0, acc, pos => some (acc, pos)
  | n + 1, acc, pos => do
    let (x, pos) ← read pos
    readMany read n (acc.push x) pos

/-- `DNSPacket::from_bytes`. -/
def Packet.fromBytes (buf : Bytes) : Option Packet := do
  if buf.size < 12 then none
  else
    let header := Header.fromBytes buf
    let (questions, pos) ← readMany (readQuestion buf) header.qdcount.toNat #[] 12
    let (answers, pos) ← readMany (readRecord buf) header.ancount.toNat #[] pos
    let (authorities, pos) ← readMany (readRecord buf) header.nscount.toNat #[] pos
    let (resources, _) ← readMany (readRecord buf) header.arcount.toNat #[] pos
    pure { header, questions, answers, authorities, resources }

/-! ## Serialization -/

def Question.toBytes (q : Question) : Bytes := q.name ++ toBe16 q.tp ++ toBe16 q.cls

/-- `ttl.saturating_sub(age)`. -/
def satSub (a b : UInt32) : UInt32 := if a ≥ b then a - b else 0

/-! ### Name compression (`Compressor`)

The compressor's `HashMap` from suffix to offset is an association list:
Rust inserts a suffix only after looking it up and missing, so keys are
unique and the first match is the only one. Loops are structural
recursion on a fuel argument (each step consumes at least one byte, so
`name.size + 1` is enough) so that the kernel can evaluate them. -/

abbrev Suffixes := List (Bytes × Nat)

def Suffixes.get? (c : Suffixes) (s : Bytes) : Option Nat := (c.find? (·.1 == s)).map (·.2)

/-- The `while let` loop of `Compressor::write`, from label offset `i`. -/
def writeNameFrom (name : Bytes) : Nat → Nat → Bytes → Suffixes → Bytes × Suffixes
  | 0, _, buf, c => (buf, c)
  | fuel + 1, i, buf, c =>
    match name[i]? with
    | none => (buf, c)
    | some len =>
      let stop := i + 1 + len.toNat
      if len = 0 ∨ len.toNat > 63 ∨ stop > name.size then
        (buf ++ name.extract i name.size, c)          -- the root, or not well formed
      else
        let suffix := name.extract i name.size
        match c.get? suffix with
        | some off => (buf ++ toBe16 (UInt16.ofNat (0xC000 ||| off)), c)
        | none =>
          let c := if buf.size < 0x4000 then (suffix, buf.size) :: c else c
          writeNameFrom name fuel stop (buf ++ name.extract i stop) c

/-- `Compressor::write`. -/
def writeName (name : Bytes) (buf : Bytes) (c : Suffixes) : Bytes × Suffixes :=
  writeNameFrom name (name.size + 1) 0 buf c

/-- `compressible_rdata`: the RFC 1035 types. -/
def compressibleRdata (tp : UInt16) : Bool :=
  (2 ≤ tp.toNat ∧ tp.toNat ≤ 9) ∨ tp.toNat = 12 ∨ tp.toNat = 14 ∨ tp.toNat = 15

/-- `name_len`. -/
def nameLenFrom (b : Bytes) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    match b[i]? with
    | none => none
    | some len =>
      if len.toNat > 63 then none
      else
        let i := i + 1 + len.toNat
        if len = 0 then (if i ≤ b.size then some i else none) else nameLenFrom b fuel i

def nameLen (b : Bytes) : Option Nat := nameLenFrom b (b.size + 1) 0

/-- `rdata_fields`: the RDATA split into (is a name, bytes). -/
def rdataFields (a : Answer) : Option (List (Bool × Bytes)) :=
  if !compressibleRdata a.tp then none
  else do
    let layout ← rdataLayout a.tp
    let rec go : List Field → Bytes → Option (List (Bool × Bytes))
      | [], rest => if rest.isEmpty then some [] else none
      | f :: fs, rest => do
        let (isName, n) ← match f with
          | .name => (nameLen rest).map (true, ·)
          | .fixed n => some (false, n)
        if n > rest.size then none
        else
          let tail ← go fs (rest.extract n rest.size)
          pure ((isName, rest.extract 0 n) :: tail)
    go layout a.data

/-- `Question::write_to`. -/
def Question.write (q : Question) (buf : Bytes) (c : Suffixes) : Bytes × Suffixes :=
  let (buf, c) := writeName q.name buf c
  (buf ++ toBe16 q.tp ++ toBe16 q.cls, c)

/-- `Answer::write_to(buf, age, names)`. `as u16` truncates. -/
def Answer.write (a : Answer) (age : UInt32) (buf : Bytes) (c : Suffixes) : Bytes × Suffixes :=
  let (buf, c) := writeName a.name buf c
  let buf := buf ++ toBe16 a.tp ++ toBe16 a.cls ++ toBe32 (satSub a.ttl age)
  let lengthAt := buf.size
  let buf := buf ++ #[0, 0]
  let (buf, c) := match rdataFields a with
    | some fields => fields.foldl (fun (acc : Bytes × Suffixes) (f : Bool × Bytes) =>
        if f.1 then writeName f.2 acc.1 acc.2 else (acc.1 ++ f.2, acc.2)) (buf, c)
    | none => (buf ++ a.data, c)
  let len := toBe16 (UInt16.ofNat (buf.size - lengthAt - 2))
  ((buf.set! lengthAt len[0]!).set! (lengthAt + 1) len[1]!, c)

/-- `Z_CD`: the CD bit within `Header::z`. -/
def Z_CD : UInt8 := 0x01

/-- The header `response_bytes` writes. Everything not listed is copied
from the query header unchanged. Of `z` (Z, AD, CD) only CD is kept. -/
def responseHeader (q : Packet) (rcode : UInt8) (nAns nAuth : Nat) : Header :=
  { q.header with
    qr := 1, ra := 1, aa := 0, tc := 0, z := q.header.z &&& Z_CD, rcode := rcode
    qdcount := UInt16.ofNat q.questions.size
    ancount := UInt16.ofNat nAns
    nscount := UInt16.ofNat nAuth
    arcount := 0 }

/-- `DNSPacket::response_bytes`. -/
def Packet.responseBytes (q : Packet) (rcode : UInt8) (answers authorities : Array Answer)
    (age : UInt32) : Bytes :=
  let acc := q.questions.foldl (fun (acc : Bytes × Suffixes) x => x.write acc.1 acc.2)
    ((responseHeader q rcode answers.size authorities.size).toBytes, [])
  ((answers ++ authorities).foldl (fun (acc : Bytes × Suffixes) a => a.write age acc.1 acc.2)
    acc).1

/-- `DNSPacket::truncated_bytes`: `buf[2] |= 0x02`. -/
def Packet.truncatedBytes (q : Packet) (rcode : UInt8) : Bytes :=
  let buf := q.responseBytes rcode #[] #[] 0
  buf.set! 2 (buf[2]! ||| 0x02)

/-- `Question::to_blocked_answer`. -/
def Question.blockedAnswer (q : Question) : Option Answer :=
  if q.tp = TYPE_A then some { name := q.name, tp := q.tp, cls := q.cls, ttl := BLOCKED_TTL,
                               data := Array.replicate 4 0 }
  else if q.tp = TYPE_AAAA then some { name := q.name, tp := q.tp, cls := q.cls,
                                       ttl := BLOCKED_TTL, data := Array.replicate 16 0 }
  else none

/-- `DNSPacket::udp_payload_limit`. -/
def Packet.udpPayloadLimit (q : Packet) : Nat :=
  let v := match q.resources.find? (·.tp = TYPE_OPT) with
    | some opt => opt.cls.toNat
    | none => DEFAULT_UDP_PAYLOAD
  max DEFAULT_UDP_PAYLOAD (min v MAX_UDP_PAYLOAD)

/-- `set_id`. -/
def setId (buf : Bytes) (id : UInt16) : Bytes :=
  (buf.set! 0 (id >>> 8).toUInt8).set! 1 id.toUInt8

/-! ## Header bits of synthesized responses

RFC 4035 §3.2.3 / RFC 6840 §5.8: the AD bit in a *response* asserts that
the server has validated every RRset in it. A non-validating server must
not set it. In a query, AD = 1 only signals that the client understands
the bit; `dig` sets it by default, and so does glibc with
`options trust-ad`. The bit is bit 5 of byte 3, which Rust folds into the
3-bit field `z` (Z, AD, CD). Before #15 `response_bytes` copied all of `z`
from the query; RFC 4035 §4.6 describes exactly that failure: "buggy name
servers that blindly copy header bits that they do not understand from
the query message to the response message".
-/

def AD_BIT : UInt8 := 0x20

/-- Of the query's Z, AD and CD bits, the response keeps only CD
(RFC 4035 §3.2.2). -/
theorem response_z_is_cd (q : Packet) (rcode : UInt8) (n m : Nat) :
    (responseHeader q rcode n m).z = q.header.z &&& Z_CD := rfl

theorem Header.toBytes_size (h : Header) : h.toBytes.size = 12 := by
  simp [Header.toBytes, toBe16]

/-- Byte 3 of anything that starts with a header is the second flag byte. -/
theorem Header.byte3 (h : Header) (rest : Bytes) : (h.toBytes ++ rest)[3]! = h.flagBytes.2 := by
  have hs := h.toBytes_size
  rw [getElem!_pos (h.toBytes ++ rest) 3 (by simp; omega)]
  rw [Array.getElem_append_left (by omega)]
  simp [Header.toBytes, toBe16]

theorem flag3_clean : ∀ z, z < 256 → ∀ r, r < 16 →
    (((1 : UInt8) <<< 7) ||| (((UInt8.ofNat z) &&& Z_CD) <<< 4) ||| UInt8.ofNat r) &&& 0x60 = 0 := by
  decide +kernel

/-! ### Serialization only appends

With compression `response_bytes` is no longer a plain concatenation, so
statements about the header need this: every write keeps the bytes
already in the buffer (it appends, or patches RDLENGTH past them). -/

/-- `b` starts with `a`. -/
def Extends (a b : Bytes) : Prop := a.size ≤ b.size ∧ ∀ i < a.size, b[i]! = a[i]!

theorem Extends.refl (a : Bytes) : Extends a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {a b c : Bytes} (h1 : Extends a b) (h2 : Extends b c) : Extends a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun i hi => by rw [h2.2 i (by have := h1.1; omega), h1.2 i hi]⟩

theorem Extends.append (a x : Bytes) : Extends a (a ++ x) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getElem!_pos (a ++ x) i (by simp; omega), getElem!_pos a i hi,
    Array.getElem_append_left hi]

theorem Extends.set {a b : Bytes} (h : Extends a b) (j : Nat) (v : UInt8) (hj : a.size ≤ j) :
    Extends a (b.set! j v) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rw [← h.2 i hi]
  have hib : i < b.size := by have := h.1; omega
  rw [getElem!_pos (b.set! j v) i (by simp; omega), getElem!_pos b i hib]
  simp only [Array.set!_eq_setIfInBounds]
  exact Array.getElem_setIfInBounds_ne hib (by omega)

theorem writeNameFrom_extends (name : Bytes) :
    ∀ fuel i buf c, Extends buf (writeNameFrom name fuel i buf c).1 := by
  intro fuel
  induction fuel with
  | zero => intro i buf c; exact Extends.refl _
  | succ fuel ih =>
    intro i buf c
    unfold writeNameFrom
    split
    · exact Extends.refl _
    · dsimp only
      split
      · exact Extends.append _ _
      · split
        · exact Extends.append _ _
        · exact Extends.trans (Extends.append _ _) (ih _ _ _)

theorem writeName_extends (name buf : Bytes) (c : Suffixes) :
    Extends buf (writeName name buf c).1 := writeNameFrom_extends name _ _ _ _

theorem Question.write_extends (q : Question) (buf : Bytes) (c : Suffixes) :
    Extends buf (q.write buf c).1 := by
  unfold Question.write
  exact Extends.trans (writeName_extends _ _ _)
    (Extends.trans (Extends.append _ _) (Extends.append _ _))

theorem fields_extends (fields : List (Bool × Bytes)) (acc : Bytes × Suffixes) :
    Extends acc.1 (fields.foldl (fun (acc : Bytes × Suffixes) (f : Bool × Bytes) =>
        if f.1 then writeName f.2 acc.1 acc.2 else (acc.1 ++ f.2, acc.2)) acc).1 := by
  induction fields generalizing acc with
  | nil => exact Extends.refl _
  | cons f fs ih =>
    simp only [List.foldl_cons]
    refine Extends.trans ?_ (ih _)
    split
    · exact writeName_extends _ _ _
    · exact Extends.append _ _

theorem Answer.write_extends (a : Answer) (age : UInt32) (buf : Bytes) (c : Suffixes) :
    Extends buf (a.write age buf c).1 := by
  unfold Answer.write
  simp only
  generalize hw : writeName a.name buf c = w
  have h1 : Extends buf w.1 := hw ▸ writeName_extends _ _ _
  generalize hb : w.1 ++ toBe16 a.tp ++ toBe16 a.cls ++ toBe32 (satSub a.ttl age) = b1
  have h2 : Extends buf b1 := hb ▸ Extends.trans h1 (Extends.trans (Extends.append _ _)
    (Extends.trans (Extends.append _ _) (Extends.append _ _)))
  have h3 : Extends buf (b1 ++ #[0, 0]) := Extends.trans h2 (Extends.append _ _)
  have h4 : Extends buf (match rdataFields a with
      | some fields => fields.foldl (fun (acc : Bytes × Suffixes) (f : Bool × Bytes) =>
          if f.1 then writeName f.2 acc.1 acc.2 else (acc.1 ++ f.2, acc.2)) (b1 ++ #[0, 0], w.2)
      | none => (b1 ++ #[0, 0] ++ a.data, w.2)).1 := by
    split
    · exact Extends.trans h3 (fields_extends _ (b1 ++ #[0, 0], w.2))
    · exact Extends.trans h3 (Extends.append _ _)
  exact (h4.set _ _ (by have := h2.1; omega)).set _ _ (by have := h2.1; omega)

theorem foldl_extends {α} (f : Bytes × Suffixes → α → Bytes × Suffixes)
    (hf : ∀ acc x, Extends acc.1 (f acc x).1) (xs : Array α) (init : Bytes × Suffixes) :
    Extends init.1 (xs.foldl f init).1 := by
  rw [← Array.foldl_toList]
  induction xs.toList generalizing init with
  | nil => exact Extends.refl _
  | cons x l ih => exact Extends.trans (hf _ _) (ih _)

/-- A response starts with its header, byte for byte. -/
theorem responseBytes_extends (q : Packet) (rcode : UInt8) (answers authorities : Array Answer)
    (age : UInt32) :
    Extends (responseHeader q rcode answers.size authorities.size).toBytes
      (q.responseBytes rcode answers authorities age) := by
  unfold Packet.responseBytes
  have hq := foldl_extends (fun (acc : Bytes × Suffixes) (x : Question) => x.write acc.1 acc.2)
    (fun acc x => Question.write_extends x acc.1 acc.2) q.questions
    ((responseHeader q rcode answers.size authorities.size).toBytes, [])
  have ha := foldl_extends (fun (acc : Bytes × Suffixes) (a : Answer) => a.write age acc.1 acc.2)
    (fun acc a => Answer.write_extends a age acc.1 acc.2) (answers ++ authorities)
    (q.questions.foldl (fun (acc : Bytes × Suffixes) x => x.write acc.1 acc.2)
      ((responseHeader q rcode answers.size authorities.size).toBytes, []))
  exact Extends.trans hq ha

theorem responseBytes_header_byte (q : Packet) (rcode : UInt8) (answers authorities : Array Answer)
    (age : UInt32) (i : Nat) (hi : i < 12) :
    (q.responseBytes rcode answers authorities age)[i]!
      = (responseHeader q rcode answers.size authorities.size).toBytes[i]! :=
  (responseBytes_extends q rcode answers authorities age).2 i
    (by rw [Header.toBytes_size]; exact hi)

/-- **R4.** Every response rdns synthesizes (cache hit, blocked name,
SERVFAIL, truncated form), for every query, RCODE, record set and age,
has Z = AD = 0. RCODEs are 4 bits: rdns only ever passes a parsed RCODE
(`& 0x0f`) or a constant. -/
def NoForgedAD : Prop :=
  ∀ (q : Packet) (rcode : UInt8) (answers authorities : Array Answer) (age : UInt32),
    rcode < 16 → (q.responseBytes rcode answers authorities age)[3]! &&& 0x60 = 0

theorem no_forged_ad : NoForgedAD := by
  intro q rcode answers authorities age hr
  rw [responseBytes_header_byte q rcode answers authorities age 3 (by decide)]
  have h3 := Header.byte3 (responseHeader q rcode answers.size authorities.size) #[]
  rw [Array.append_empty] at h3
  rw [h3]
  have := flag3_clean q.header.z.toNat q.header.z.toNat_lt rcode.toNat
    (by rw [UInt8.lt_iff_toNat_lt] at hr; simpa using hr)
  simpa [responseHeader, Header.flagBytes] using this

/-- A query exactly as `dig example.com` sends it (flags `0x0120`: RD and
AD set). -/
def digQuery : Packet :=
  { header := Header.ofBytes 0x12 0x34 0x01 0x20 0 1 0 0 0 0 0 0
    questions := #[{ name := #[7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0],
                     tp := TYPE_A, cls := 1 }]
    answers := #[], authorities := #[], resources := #[] }

/-- The former counterexample: byte 3 of the reply to `dig`'s query was
`0xA0` (RA | AD); it is now `0x80` (RA). -/
example : (digQuery.responseBytes RCODE_NOERROR #[] #[] 0)[3]! = 0x80 := by decide

/-! ## Opcode

RFC 1035 §4.1.1 defines OPCODE 0 as a standard query. rdns never looks at
the opcode, so an IQUERY (1), STATUS (2), NOTIFY (4) or UPDATE (5) message
that carries a question is answered from the blocklist or the cache as if
it were a QUERY, echoing the opcode back, instead of NOTIMP (RFC 1035
§4.1.1, RFC 2136 §3.1). -/
theorem response_copies_opcode (q : Packet) (rcode : UInt8) (n m : Nat) :
    (responseHeader q rcode n m).opcode = q.header.opcode := rfl

/-! ## R1 -/

/-- **R1 (header part).** `response_bytes` sets QR, clears TC and AA, and
uses the given RCODE, for every query. -/
theorem r1_response_header (q : Packet) (rcode : UInt8) (n m : Nat) :
    let h := responseHeader q rcode n m
    h.qr = 1 ∧ h.tc = 0 ∧ h.aa = 0 ∧ h.rcode = rcode ∧ h.packetId = q.header.packetId :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


/-! ## EDNS (RFC 6891 §7)

"If an OPT record is present in a received request, compliant responders
MUST include an OPT record in their respective responses." -/

/-- `response_bytes` never writes an additional section. -/
theorem response_arcount_zero (q : Packet) (rcode : UInt8) (n m : Nat) :
    (responseHeader q rcode n m).arcount = 0 := rfl

def Packet.hasOpt (q : Packet) : Bool := q.resources.any (·.tp = TYPE_OPT)

/-- **RFC 6891 §7**, for the responses rdns synthesizes. -/
def OptEchoed (respond : Packet → Bytes) : Prop :=
  ∀ q : Packet, q.hasOpt = true → (respond q)[11]! ≠ 0

/-- `dig`'s default query, with its OPT record (UDP size 1232). -/
def digQueryEdns : Packet :=
  { digQuery with
    header := { digQuery.header with arcount := 1 }
    resources := #[{ name := #[0], tp := TYPE_OPT, cls := 1232, ttl := 0, data := #[] }] }

/-- **Counterexample.** A cache hit, blocked answer or SERVFAIL for an EDNS
query has ARCOUNT = 0. -/
theorem bug_opt_missing :
    ¬ OptEchoed (fun q => q.responseBytes RCODE_NOERROR #[] #[] 0) := fun h =>
  absurd (h digQueryEdns (by decide +kernel)) (by decide +kernel)

/-! ## Cache hits lose name compression

`response_bytes` writes every name in full, while the upstream's message
used compression pointers. A cache hit can therefore be much larger than
the response it was built from, and for a client without EDNS (512 bytes;
glibc's default) it goes over the limit and `reply` sends TC = 1 with no
answers instead. rdns has no TCP, so the first lookup works and every
later one, until the entry expires, fails. -/

def wireName (labels : List (List UInt8)) : Bytes :=
  (labels.foldl (fun acc l => acc ++ #[UInt8.ofNat l.length] ++ l.toArray) #[]).push 0

def str (s : String) : List UInt8 := s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- `_ldap._tcp.dc._msdcs.corp.example.com`, the SRV name every Active
Directory client looks up. `corp.example.com` starts at offset 12 + 21. -/
def adName : Bytes :=
  wireName [str "_ldap", str "_tcp", str "dc", str "_msdcs", str "corp", str "example", str "com"]

def corpName : Bytes := wireName [str "corp", str "example", str "com"]

/-- Target `dcN.corp.example.com`, compressed as upstreams send it. -/
def srvTarget (i : Nat) : Bytes := #[3, 100, 99, UInt8.ofNat (48 + i), 0xC0, 33]

def srvRdata (i : Nat) : Bytes := #[0, 0, 0, 100, 1, 133] ++ srvTarget i

/-- An upstream's answer: 10 SRV records, owner names and targets compressed. -/
def srvRaw : Bytes :=
  #[0x12, 0x34, 0x81, 0x80, 0, 1, 0, 10, 0, 0, 0, 0] ++ adName ++ #[0, 33, 0, 1]
    ++ (List.range 10).foldl (fun acc i =>
        acc ++ #[0xC0, 12, 0, 33, 0, 1, 0, 0, 14, 16, 0, (srvRdata i).size.toUInt8]
          ++ srvRdata i) #[]

/-- The same records as `from_bytes` decodes them: every name in full. -/
def srvParsed : Packet :=
  { header := Header.ofBytes 0x12 0x34 0x81 0x80 0 1 0 10 0 0 0 0
    questions := #[{ name := adName, tp := 33, cls := 1 }]
    answers := (List.range 10).toArray.map (fun i =>
      { name := adName, tp := 33, cls := 1, ttl := 3600,
        data := #[0, 0, 0, 100, 1, 133, 3, 100, 99, UInt8.ofNat (48 + i)] ++ corpName })
    authorities := #[], resources := #[] }

/-! The link between the two is checked by running the model (the same
code the differential test compares with rdns), not by the kernel: the
kernel can't evaluate `readName`, which is defined by well-founded
recursion. -/
#guard Packet.fromBytes srvRaw == some srvParsed

/-- **The former counterexample (compression).** The upstream's response
is 295 bytes and fits a 512-byte client. Before #17 the cache hit rebuilt
from the same records was 825 bytes, so that client got TC = 1 and no
answers; with compression it is 455 bytes (SRV targets stay uncompressed,
RFC 2782) and fits. -/
theorem cache_hit_fits_after_compression :
    srvRaw.size = 295 ∧
    (srvParsed.responseBytes RCODE_NOERROR srvParsed.answers #[] 1).size = 455 := by
  decide +kernel

end Rdns
