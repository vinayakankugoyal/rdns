import Std.Tactic.BVDecide

/-!
# Wire primitives and the DNS header (`src/packet.rs`, `Header`)

A line-by-line model of `Header::from_bytes` and `Header::write_to`.
Rust's `u8`/`u16` are modelled with Lean's `UInt8`/`UInt16`, whose shifts
and bitwise operations wrap exactly like Rust's (shift amounts are always
below the bit width here, so Rust never panics).
-/

namespace Rdns

abbrev Bytes := Array UInt8

/-- `u16::from_be_bytes([hi, lo])`. -/
def be16 (hi lo : UInt8) : UInt16 := (hi.toUInt16 <<< 8) ||| lo.toUInt16

/-- `u16::to_be_bytes`. -/
def toBe16 (x : UInt16) : Bytes := #[(x >>> 8).toUInt8, x.toUInt8]

/-- `u32::from_be_bytes([a, b, c, d])`. -/
def be32 (a b c d : UInt8) : UInt32 :=
  (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32

/-- `u32::to_be_bytes`. -/
def toBe32 (x : UInt32) : Bytes :=
  #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

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

theorem toBe16_be16 (hi lo : UInt8) : toBe16 (be16 hi lo) = #[hi, lo] := by
  have h1 : ((be16 hi lo) >>> 8).toUInt8 = hi := by
    unfold be16; bv_decide
  have h2 : (be16 hi lo).toUInt8 = lo := by
    unfold be16; bv_decide
  simp [toBe16, h1, h2]

/-- **H1, flag bytes.** Writing a parsed header reproduces both flag bytes,
for all 2¹⁶ values. Proved by bit-blasting, so it covers every input. -/
theorem h1_flags (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt8) :
    (Header.ofBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11).flagBytes = (b2, b3) := by
  simp only [Header.ofBytes, Header.flagBytes, Prod.mk.injEq]
  constructor <;> bv_decide

/-- **H1.** `write(read(b)) = b` for every 12-byte header `b`. -/
theorem h1_header_roundtrip (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : UInt8) :
    (Header.ofBytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11).toBytes
      = #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] := by
  have hf := h1_flags b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  simp only [Header.toBytes, hf]
  simp only [Header.ofBytes, toBe16_be16]
  rfl

end Rdns
