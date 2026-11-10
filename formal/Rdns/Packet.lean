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

/-- `Answer::write_to(buf, age)`. `data.len() as u16` truncates. -/
def Answer.toBytes (a : Answer) (age : UInt32) : Bytes :=
  a.name ++ toBe16 a.tp ++ toBe16 a.cls ++ toBe32 (satSub a.ttl age)
    ++ toBe16 (UInt16.ofNat a.data.size) ++ a.data

/-- The header `response_bytes` writes. Everything not listed is copied
from the query header unchanged. -/
def responseHeader (q : Packet) (rcode : UInt8) (nAns nAuth : Nat) : Header :=
  { q.header with
    qr := 1, ra := 1, aa := 0, tc := 0, rcode := rcode
    qdcount := UInt16.ofNat q.questions.size
    ancount := UInt16.ofNat nAns
    nscount := UInt16.ofNat nAuth
    arcount := if (q.resources.find? (·.tp = TYPE_OPT)).isSome then 1 else 0 }

/-- The OPT record `response_bytes` appends when the query has one: root
owner, type 41, class 4096 (`MAX_UDP_PAYLOAD`), TTL = the query's DO bit
(extended RCODE 0, version 0), no RDATA (#23). -/
def optRecord (q : Packet) : Bytes :=
  match q.resources.find? (·.tp = TYPE_OPT) with
  | some opt => #[0] ++ toBe16 TYPE_OPT ++ toBe16 (UInt16.ofNat MAX_UDP_PAYLOAD)
      ++ toBe32 (opt.ttl &&& 0x8000) ++ #[0, 0]
  | none => #[]

/-- `DNSPacket::response_bytes`. -/
def Packet.responseBytes (q : Packet) (rcode : UInt8) (answers authorities : Array Answer)
    (age : UInt32) : Bytes :=
  (responseHeader q rcode answers.size authorities.size).toBytes
    ++ (q.questions.foldl (fun acc x => acc ++ x.toBytes) #[])
    ++ ((answers ++ authorities).foldl (fun acc a => acc ++ a.toBytes age) #[])
    ++ optRecord q

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
3-bit field `z` (Z, AD, CD) and so copies from the query.
-/

def AD_BIT : UInt8 := 0x20

/-- Byte 3 of the header `response_bytes` writes always carries the query's
Z, AD and CD bits, for every query. This states the defect; a fix (clearing
Z and AD) makes it false, and `bug_ad_bit_forged` turns into a proof of
`NoForgedAD`. Copying CD is correct (RFC 4035 §3.2.2); copying AD and Z is
not (RFC 4035 §3.2.3, RFC 1035 §4.1.1: Z "must be zero"). RFC 4035 §4.6
describes this exact failure: "buggy name servers that blindly copy header
bits that they do not understand from the query message to the response
message". -/
theorem response_copies_z (q : Packet) (rcode : UInt8) (n m : Nat) :
    (responseHeader q rcode n m).z = q.header.z := rfl

/-- What rdns should guarantee: a response it synthesizes (cache hit,
blocked name, SERVFAIL) never claims AD, since rdns validates nothing. -/
def NoForgedAD (respond : Packet → Bytes) : Prop :=
  ∀ q : Packet, (respond q)[3]! &&& AD_BIT = 0

/-- A query exactly as `dig example.com` sends it (flags `0x0120`: RD and
AD set; with an EDNS OPT record, which doesn't matter here). -/
def digQuery : Packet :=
  { header := Header.ofBytes 0x12 0x34 0x01 0x20 0 1 0 0 0 0 0 0
    questions := #[{ name := #[7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0],
                     tp := TYPE_A, cls := 1 }]
    answers := #[], authorities := #[], resources := #[] }

/-- **Counterexample (AD).** The cached/blocked/SERVFAIL response to
`dig`'s default query has AD = 1, so `NoForgedAD` is false, for every
RCODE, answer set and age. -/
theorem bug_ad_bit_forged :
    ¬ NoForgedAD (fun q => q.responseBytes RCODE_NOERROR #[] #[] 0) := by
  intro h
  have := h digQuery
  revert this
  decide

/-- The same, stated directly on the bytes: byte 3 is `0xA0`, RA and AD. -/
example : (digQuery.responseBytes RCODE_NOERROR #[] #[] 0)[3]! = 0xA0 := by decide

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

def Packet.hasOpt (q : Packet) : Bool := (q.resources.find? (·.tp = TYPE_OPT)).isSome

/-- **R5, RFC 6891 §7**, for the responses rdns synthesizes. -/
def OptEchoed : Prop :=
  ∀ (q : Packet) (rcode : UInt8) (answers authorities : Array Answer) (age : UInt32),
    (q.responseBytes rcode answers authorities age)[11]! = if q.hasOpt then 1 else 0

theorem Header.toBytes_size (h : Header) : h.toBytes.size = 12 := by
  simp [Header.toBytes, toBe16]

/-- Byte 11 of anything that starts with a header is ARCOUNT's low byte. -/
theorem Header.byte11 (h : Header) (rest : Bytes) :
    (h.toBytes ++ rest)[11]! = UInt8.ofNat (h.arcount.toNat % 256) := by
  have hs := h.toBytes_size
  rw [getElem!_pos (h.toBytes ++ rest) 11 (by simp; omega)]
  rw [Array.getElem_append_left (by omega)]
  simp [Header.toBytes, toBe16]

/-- Every synthesized response to a query with an OPT record says it has
one additional record (the OPT record `optRecord` appends), and one to a
query without OPT says none. Until #23 ARCOUNT was always 0. -/
theorem opt_echoed : OptEchoed := by
  intro q rcode answers authorities age
  simp only [Packet.responseBytes, Array.append_assoc, Header.byte11, responseHeader,
    Packet.hasOpt]
  split <;> next h => simp [h]

/-- `dig`'s default query, with its OPT record (UDP size 1232). -/
def digQueryEdns : Packet :=
  { digQuery with
    header := { digQuery.header with arcount := 1 }
    resources := #[{ name := #[0], tp := TYPE_OPT, cls := 1232, ttl := 0, data := #[] }] }

/-- The former counterexample: the response to `dig`'s EDNS query now ends
in an OPT record. -/
example : (digQueryEdns.responseBytes RCODE_NOERROR #[] #[] 0).extract 29 40
    = #[0, 0, 41, 16, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel

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

/-- **Counterexample (compression).** The upstream's response is 295 bytes
and fits a 512-byte client; the cache hit rebuilt from the same records is
825 bytes, so that client gets TC = 1 and no answers. -/
theorem bug_cache_hit_loses_compression :
    srvRaw.size = 295 ∧
    (srvParsed.responseBytes RCODE_NOERROR srvParsed.answers #[] 1).size = 825 := by
  decide +kernel

end Rdns
