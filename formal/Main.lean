import Rdns

/-!
Differential-testing front end. Reads one hex-encoded message per line on
stdin and prints, per line, everything the model computes from it:
the parse, `cache_ttl`, `response_bytes`, `truncated_bytes` and
`udp_payload_limit`. `differential/` prints the same line from the Rust
code; the two outputs must be identical.
-/

open Rdns

def hexDigit (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else none

def fromHex (s : String) : Option Bytes := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then return none
  let mut out : Bytes := #[]
  for i in [0:cs.size / 2] do
    match hexDigit cs[2 * i]!, hexDigit cs[2 * i + 1]! with
    | some a, some b => out := out.push (a * 16 + b)
    | _, _ => return none
  return some out

def hexChars : Array Char := "0123456789abcdef".toList.toArray

def toHex (b : Bytes) : String :=
  b.foldl (fun s x => (s.push hexChars[(x / 16).toNat]!).push hexChars[(x % 16).toNat]!) ""

def renderQ (q : Question) : String := s!"{toHex q.name}.{q.tp}.{q.cls}"
def renderA (a : Answer) : String := s!"{toHex a.name}.{a.tp}.{a.cls}.{a.ttl}.{toHex a.data}"

def renderList {α} (f : α → String) (xs : Array α) : String :=
  ";".intercalate (xs.toList.map f)

def render (buf : Bytes) : String :=
  match Packet.fromBytes buf with
  | none => "none"
  | some p =>
    let ttl := match cacheTtl p with | some t => toString t | none => "-"
    let h := p.header
    s!"H:{h.packetId}.{h.qr}.{h.opcode}.{h.aa}.{h.tc}.{h.rd}.{h.ra}.{h.z}.{h.rcode}"
      ++ s!".{h.qdcount}.{h.ancount}.{h.nscount}.{h.arcount}|Q:{renderList renderQ p.questions}"
      ++ s!"|A:{renderList renderA p.answers}|N:{renderList renderA p.authorities}"
      ++ s!"|R:{renderList renderA p.resources}|ttl:{ttl}"
      ++ s!"|resp:{toHex (p.responseBytes p.header.rcode p.answers p.authorities 7)}"
      ++ s!"|tr:{toHex (p.truncatedBytes p.header.rcode)}|lim:{p.udpPayloadLimit}"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.toString
  match fromHex line with
  | some buf => stdout.putStrLn (render buf)
  | none => stdout.putStrLn "badhex"
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
