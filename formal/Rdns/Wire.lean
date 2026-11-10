/-!
# Wire primitives and the DNS header (`src/packet.rs`, `Header`)

A line-by-line model of `Header::from_bytes` and `Header::write_to`.
Rust's `u8`/`u16` are modelled with Lean's `UInt8`/`UInt16`, whose shifts
and bitwise operations wrap exactly like Rust's (shift amounts are always
below the bit width here, so Rust never panics). The standard library's
`from_be_bytes`/`to_be_bytes` are modelled by what they compute,
`hi·256 + lo` and its digits.

Every proof in `formal/` is checked by Lean's kernel alone: no
`bv_decide`, `native_decide` or other tactic that trusts compiled code.
-/

namespace Rdns

abbrev Bytes := Array UInt8

/-- `u16::from_be_bytes([hi, lo])`. -/
def be16 (hi lo : UInt8) : UInt16 := UInt16.ofNat (hi.toNat * 256 + lo.toNat)

/-- `u16::to_be_bytes`. -/
def toBe16 (x : UInt16) : Bytes := #[UInt8.ofNat (x.toNat / 256), UInt8.ofNat (x.toNat % 256)]

/-- `u32::from_be_bytes([a, b, c, d])`. -/
def be32 (a b c d : UInt8) : UInt32 :=
  UInt32.ofNat (((a.toNat * 256 + b.toNat) * 256 + c.toNat) * 256 + d.toNat)

/-- `u32::to_be_bytes`. -/
def toBe32 (x : UInt32) : Bytes :=
  #[UInt8.ofNat (x.toNat / 16777216), UInt8.ofNat (x.toNat / 65536 % 256),
    UInt8.ofNat (x.toNat / 256 % 256), UInt8.ofNat (x.toNat % 256)]

structure Header where
  packetId : UInt16
  qr : UInt8
  opcode : UInt8
  aa : UInt8
  tc : UInt8
  rd : UInt8
  ra : UInt8
  /-- The three bits Rust calls `z`: Z (bit 6), AD (bit 5) and CD (bit 4)
  of byte 3 (RFC 1035 §4.1.1, RFC 4035 §3.2). -/
  z : UInt8
  rcode : UInt8
  qdcount : UInt16
  ancount : UInt16
  nscount : UInt16
  arcount : UInt16
  deriving Repr, DecidableEq, Inhabited

/-- `Header::from_bytes`. Rust indexes `buf[0..12]` directly; callers pass
a slice of exactly 12 bytes, so the model takes the bytes individually.
Rust's `>>` binds tighter than `&`, so `buf[2] >> 7 & 0x01` is
`(buf[2] >> 7) & 0x01`. -/
def Header.ofBytes (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt8) : Header :=
  { packetId := be16 b0 b1
    qr := (b2 >>> 7) &&& 0x01
    opcode := (b2 >>> 3) &&& 0x0f
    aa := (b2 >>> 2) &&& 0x01
    tc := (b2 >>> 1) &&& 0x01
    rd := b2 &&& 0x01
    ra := (b3 >>> 7) &&& 0x01
    z := (b3 >>> 4) &&& 0x07
    rcode := b3 &&& 0x0f
    qdcount := be16 b4 b5
    ancount := be16 b6 b7
    nscount := be16 b8 b9
    arcount := be16 b10 b11 }

/-- `Header::from_bytes` on a buffer of at least 12 bytes. -/
def Header.fromBytes (buf : Bytes) : Header :=
  Header.ofBytes buf[0]! buf[1]! buf[2]! buf[3]! buf[4]! buf[5]!
    buf[6]! buf[7]! buf[8]! buf[9]! buf[10]! buf[11]!

/-- The two flag bytes `Header::write_to` produces. Rust's `<<` binds
tighter than `|`. -/
def Header.flagBytes (h : Header) : UInt8 × UInt8 :=
  ( (h.qr <<< 7) ||| (h.opcode <<< 3) ||| (h.aa <<< 2) ||| (h.tc <<< 1) ||| h.rd
  , (h.ra <<< 7) ||| (h.z <<< 4) ||| h.rcode )

/-- `Header::write_to`. -/
def Header.toBytes (h : Header) : Bytes :=
  toBe16 h.packetId ++ #[h.flagBytes.1, h.flagBytes.2] ++ toBe16 h.qdcount
    ++ toBe16 h.ancount ++ toBe16 h.nscount ++ toBe16 h.arcount

/-! ## Properties -/

/-- Reduce a statement about every `UInt8` to one about `0..255`, which
`decide` can check by enumeration. -/
theorem UInt8.forall_of_lt {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n))
    (b : UInt8) : P b := by
  simpa using h b.toNat b.toNat_lt

theorem toBe16_be16 (hi lo : UInt8) : toBe16 (be16 hi lo) = #[hi, lo] := by
  have h1 := hi.toNat_lt
  have h2 := lo.toNat_lt
  have hv : (be16 hi lo).toNat = hi.toNat * 256 + lo.toNat := by
    simp only [be16, UInt16.toNat_ofNat']; omega
  simp only [toBe16, hv]
  have e1 : (hi.toNat * 256 + lo.toNat) / 256 = hi.toNat := by omega
  have e2 : (hi.toNat * 256 + lo.toNat) % 256 = lo.toNat := by omega
  simp [e1, e2]

/-- Byte 2 as `write_to` rebuilds it from the fields `from_bytes` extracts. -/
def flag2 (b : UInt8) : UInt8 :=
  (((b >>> 7) &&& 0x01) <<< 7) ||| (((b >>> 3) &&& 0x0f) <<< 3) ||| (((b >>> 2) &&& 0x01) <<< 2)
    ||| (((b >>> 1) &&& 0x01) <<< 1) ||| (b &&& 0x01)

/-- Byte 3, likewise. -/
def flag3 (b : UInt8) : UInt8 :=
  (((b >>> 7) &&& 0x01) <<< 7) ||| (((b >>> 4) &&& 0x07) <<< 4) ||| (b &&& 0x0f)

theorem flag2_id : ∀ b, flag2 b = b :=
  UInt8.forall_of_lt (P := fun b => flag2 b = b) (by decide +kernel)

theorem flag3_id : ∀ b, flag3 b = b :=
  UInt8.forall_of_lt (P := fun b => flag3 b = b) (by decide +kernel)

/-- **H1, flag bytes.** Writing a parsed header reproduces both flag bytes,
for all 2¹⁶ values (each byte is checked by enumerating its 256 values). -/
theorem h1_flags (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt8) :
    (Header.ofBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11).flagBytes = (b2, b3) := by
  have e2 := flag2_id b2
  have e3 := flag3_id b3
  simp only [flag2, flag3] at e2 e3
  simp only [Header.ofBytes, Header.flagBytes, e2, e3]

/-- **H1.** `write(read(b)) = b` for every 12-byte header `b`. -/
theorem h1_header_roundtrip (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt8) :
    (Header.ofBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11).toBytes
      = #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] := by
  have hf := h1_flags b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  simp only [Header.toBytes, hf]
  simp only [Header.ofBytes, toBe16_be16]
  rfl

end Rdns
