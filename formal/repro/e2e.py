"""End-to-end reproductions of the bugs the Lean model found, against the
real rdns binary.

Starts a scripted upstream on 127.0.0.1:5300, runs rdns on 127.0.0.1:5353
pointed at it, and sends queries as real clients would. Usage:

    cargo build --release
    python3 formal/repro/e2e.py target/release/rdns
"""
import socket, struct, subprocess, sys, threading, time, os

RDNS = sys.argv[1]
UP = ("127.0.0.1", 5300)
RD = ("127.0.0.1", 5353)

def wire(name):
    out = b""
    for l in name.split("."):
        out += bytes([len(l)]) + l.encode()
    return out + b"\0"

def parse_name(m, i):
    labels = []
    while True:
        b = m[i]
        if b & 0xC0 == 0xC0:
            ptr = ((b & 0x3F) << 8) | m[i + 1]
            return ".".join(labels + ([parse_name(m, ptr)[0]] if True else [])).strip("."), i + 2
        if b == 0:
            return ".".join(labels), i + 1
        labels.append(m[i + 1:i + 1 + b].decode(errors="replace"))
        i += 1 + b

def rr(name, tp, ttl, rdata):
    return wire(name) + struct.pack(">HHIH", tp, 1, ttl, len(rdata)) + rdata

def soa(zone, ttl, minimum):
    rdata = wire("ns." + zone) + wire("admin." + zone) + struct.pack(">IIIII", 1, 7200, 900, 86400, minimum)
    return rr(zone, 6, ttl, rdata)

upstream_log = []

def upstream():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.bind(UP)
    while True:
        q, addr = s.recvfrom(4096)
        qid, flags = struct.unpack(">HH", q[:4])
        name, i = parse_name(q, 12)
        qtype = struct.unpack(">H", q[i:i + 2])[0]
        question = q[12:i + 4]
        cd = bool(flags & 0x0010)
        upstream_log.append((name, qtype, cd))
        rcode, an, ns = 0, [], []
        if name == "ad.test":
            an = [rr(name, 1, 300, bytes([192, 0, 2, 1]))]
        elif name == "bogus.test":
            # A validating upstream: the zone's signatures are broken.
            if cd:
                an = [rr(name, 1, 3600, bytes([203, 0, 113, 66]))]
            else:
                rcode = 2
        elif name == "www.nx.test":
            an = [rr(name, 5, 1, wire("gone.nx.test"))]
            ns = [soa("nx.test", 3600, 3600)]
            rcode = 3
        elif name == "v6.cdn.test":
            an = [rr(name, 5, 3600, wire("edge.cdn.test"))]
            ns = [soa("cdn.test", 2, 2)]
        elif name == "neg.test":
            ns = [soa("neg.test", 3600, 2)]
            rcode = 3
        elif name == "_ldap._tcp.dc._msdcs.corp.example.com":
            off = 12 + 21  # "corp.example.com" inside the question
            for k in range(10):
                rdata = struct.pack(">HHH", 0, 100, 389) + bytes([3]) + b"dc" + bytes([48 + k]) + bytes([0xC0, off])
                an.append(bytes([0xC0, 12]) + struct.pack(">HHIH", 33, 1, 3600, len(rdata)) + rdata)
        elif name == "signed-nx.test":
            ns = [soa("signed-nx.test", 300, 300),
                  rr("signed-nx.test", 47, 300, wire("z.signed-nx.test") + bytes([0, 6, 0x22, 0, 0, 0, 3])),
                  rr("signed-nx.test", 46, 300, bytes([0, 6, 13, 2]) + bytes(14) + wire("signed-nx.test") + bytes(64))]
            rcode = 3
        elif name == "big.test":
            an = [rr(name, 1, 0xFFFFFFFF, bytes([192, 0, 2, 9]))]
        resp = struct.pack(">HHHHHH", qid, 0x8180 | rcode, 1, len(an), len(ns), 0) + question + b"".join(an) + b"".join(ns)
        s.sendto(resp, addr)

def query(name, qtype=1, flags=0x0100, opcode=0):
    flags |= opcode << 11
    q = struct.pack(">HHHHHH", 0xBEEF, flags, 1, 0, 0, 0) + wire(name) + struct.pack(">HH", qtype, 1)
    c = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    c.settimeout(8)
    c.sendto(q, RD)
    m, _ = c.recvfrom(65535)
    fl = struct.unpack(">H", m[2:4])[0]
    qd, an, ns, ar = struct.unpack(">HHHH", m[4:12])
    name_, i = parse_name(m, 12)
    i += 4
    recs = []
    for _ in range(an + ns):
        n, i = parse_name(m, i)
        tp, cl, ttl, ln = struct.unpack(">HHIH", m[i:i + 10])
        rd = m[i + 10:i + 10 + ln]
        recs.append((n, tp, ttl, rd))
        i += 10 + ln
    return {
        "opcode": (fl >> 11) & 0xF, "AD": bool(fl & 0x20), "CD": bool(fl & 0x10), "rcode": fl & 0xF,
        "an": recs[:an], "ns": recs[an:], "ar": ar,
    }

def show(label, r):
    an = [(n, tp, ttl) for n, tp, ttl, _ in r["an"]]
    ns = [(n, tp, ttl, struct.unpack(">I", rd[-4:])[0] if tp == 6 else None) for n, tp, ttl, rd in r["ns"]]
    print(f"  {label}: opcode={r['opcode']} rcode={r['rcode']} AD={int(r['AD'])} answers={an} authority(name,type,ttl,MINIMUM)={ns} arcount={r['ar']}")

threading.Thread(target=upstream, daemon=True).start()
time.sleep(0.2)
proc = subprocess.Popen([RDNS, "--no-tui", "--port", "5353", "--resolver", "%s:%d" % UP],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
time.sleep(1.0)
try:
    print("1. AD bit (query flags 0x0120, as `dig` sends them)")
    show("first (relayed from upstream)", query("ad.test", flags=0x0120))
    show("second (cache hit)", query("ad.test", flags=0x0120))

    print("2. CD bit: validating upstream, broken DNSSEC on bogus.test")
    show("client A, CD=0", query("bogus.test"))
    show("client B, CD=1", query("bogus.test", flags=0x0110))
    show("client A again, CD=0", query("bogus.test"))
    print("   upstream saw:", [x for x in upstream_log if x[0] == "bogus.test"])

    print("3a. NXDOMAIN behind a CNAME (CNAME TTL 1, negative TTL 3600)")
    show("t=0", query("www.nx.test"))
    time.sleep(3)
    show("t=3s, CNAME expired 2s ago", query("www.nx.test"))
    print("   upstream asked", sum(1 for x in upstream_log if x[0] == "www.nx.test"), "time(s)")

    print("3b. NODATA behind a CNAME (CNAME TTL 3600, negative TTL 2)")
    show("t=0", query("v6.cdn.test", qtype=28))
    time.sleep(3)
    show("t=3s, negative TTL expired 1s ago", query("v6.cdn.test", qtype=28))
    print("   upstream asked", sum(1 for x in upstream_log if x[0] == "v6.cdn.test"), "time(s)")

    print("4. Negative TTL: NXDOMAIN, SOA TTL 3600, MINIMUM 2 (negative TTL 2 s)")
    show("t=0", query("neg.test"))
    time.sleep(1.5)
    show("t=1.5s, cache hit", query("neg.test"))

    print("9. Compression lost on cache hits (10 SRV records, client without EDNS)")
    for label in ["first (relayed)", "second (cache hit)"]:
        q = struct.pack(">HHHHHH", 0xBEEF, 0x0100, 1, 0, 0, 0) + wire("_ldap._tcp.dc._msdcs.corp.example.com") + struct.pack(">HH", 33, 1)
        c = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); c.settimeout(8); c.sendto(q, RD)
        m, _ = c.recvfrom(65535)
        fl = struct.unpack(">H", m[2:4])[0]
        print(f"  {label}: {len(m)} bytes, TC={int(bool(fl & 0x200))}, ancount={struct.unpack('>H', m[6:8])[0]}")
    print("10. Signed NXDOMAIN (SOA, NSEC, RRSIG in authority)")
    for label in ["first (relayed)", "second (cache hit)"]:
        r = query("signed-nx.test")
        print(f"  {label}: authority types = {[tp for _, tp, _, _ in r['ns']]}")
    print("5. TTL 0xFFFFFFFF")
    show("first", query("big.test"))
    show("second (cache hit)", query("big.test"))

    print("7. Opcode NOTIFY (4) for a cached name")
    show("NOTIFY", query("ad.test", opcode=4, flags=0))

    print("8. EDNS: query with an OPT record (payload 1232)")
    opt = b"\0" + struct.pack(">HHIH", 41, 1232, 0, 0)
    q = struct.pack(">HHHHHH", 0xBEEF, 0x0100, 1, 0, 0, 1) + wire("ad.test") + struct.pack(">HH", 1, 1) + opt
    c = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); c.settimeout(8); c.sendto(q, RD)
    m, _ = c.recvfrom(65535)
    print("  cache hit to an EDNS query: arcount =", struct.unpack(">H", m[10:12])[0])
finally:
    proc.kill()
