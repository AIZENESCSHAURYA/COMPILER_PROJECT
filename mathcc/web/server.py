#!/usr/bin/env python3
"""Local web server for mathcc: serves the frontend and runs the real compiler binary.

    python3 web/server.py            # then open http://127.0.0.1:8000
"""
import json, os, re, subprocess, sys, tempfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "bin", "mathcc")
STATIC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "static")
EXAMPLES = os.path.join(ROOT, "examples")
MAX_SOURCE = 20000

def parse_compile(text):
    """Turn mathcc's report into structured data."""
    res = {"inputs": "", "outputs": [], "evaluation": [], "cert": None, "verify": [], "bench": [], "wrote": None}
    cur, section, tac_mode = None, None, False
    for line in text.splitlines():
        if line.startswith("mathcc |"):
            res["inputs"] = line.split("inputs:", 1)[-1].strip(); continue
        m = re.match(r"^\[(.+)\]$", line)
        if m:
            cur = {"name": m.group(1), "original": "", "simplified": "", "guards": [], "proven": 0, "runtimeGuards": 0,
                   "skipped": "", "size": {}, "stability": "", "tac": [], "result": "", "guardNotes": "", "noGuard": True, "why": [], "skips": []}
            res["outputs"].append(cur); section = "out"; tac_mode = False; continue
        if line.startswith("evaluation:"): section, cur = "eval", None; continue
        if line.startswith("certificate check"): section, cur = "cert", None; res["cert"] = {"notes": []}; continue
        if line.startswith("end-to-end verification"): section, cur = "verify", None; continue
        if line.startswith("benchmark"): section, cur = "bench", None; continue
        if line.startswith("wrote "): res["wrote"] = line[6:]; continue
        if section == "out" and cur is not None:
            if line.startswith("  original  :"): cur["original"] = line.split(":", 1)[1].strip()
            elif line.startswith("  simplified:"): cur["simplified"] = line.split(":", 1)[1].strip()
            elif line.startswith("  guards    :"):
                body = line.split(":", 1)[1].strip(); tac_mode = False
                mm = re.search(r"(\d+) side condition", body)
                if mm: cur["proven"] = int(mm.group(1))
                mm = re.match(r"(\d+) runtime check", body)
                if mm: cur["runtimeGuards"] = int(mm.group(1)); cur["noGuard"] = False
            elif line.startswith("              - "): cur["guards"].append(line.split("- ", 1)[1].strip())
            elif line.startswith("              ("):
                mm = re.search(r"(\d+) more proven", line)
                if mm: cur["proven"] = int(mm.group(1))
            elif line.startswith("  skipped   :"): cur["skipped"] = line.split(":", 1)[1].strip()
            elif line.startswith("  size      :"):
                mm = re.search(r"DAG (\d+) -> (\d+) nodes ; VM (\d+) -> (\d+)", line)
                if mm: cur["size"] = dict(zip(["dagFrom", "dagTo", "vmFrom", "vmTo"], map(int, mm.groups())))
            elif line.startswith("  stability:"): cur["stability"] = line.strip()
            elif line.startswith("  why:"): tac_mode = False
            elif line.startswith("    step|"):
                parts = line.strip().split("|")
                gs = []
                if len(parts) > 4 and parts[4]:
                    for g in parts[4].split(";"):
                        txt, _, st = g.rpartition("~"); gs.append({"text": txt, "status": {"P": "proven", "R": "runtime", "I": "ignored"}.get(st, "runtime")})
                cur["why"].append({"rule": parts[1], "pre": parts[2], "post": parts[3], "guards": gs})
            elif line.startswith("    skip|"):
                parts = line.strip().split("|", 2); cur["skips"].append({"guard": parts[1], "reason": parts[2] if len(parts) > 2 else ""})
            elif line.startswith("  three-address code"): tac_mode = True
            elif tac_mode and line.startswith("    "):
                s = line.strip()
                if s.startswith("result ="): cur["result"] = s
                elif s.startswith("guard "): pass
                else: cur["tac"].append(s)
        elif section == "eval" and line.startswith("  "):
            mm = re.match(r"^\s+(\S+)\s+original = (\S+)\s+compiled = (\S+)\s*(\(.*\))?", line)
            if mm: res["evaluation"].append({"name": mm.group(1), "original": mm.group(2), "compiled": mm.group(3), "fallback": bool(mm.group(4))})
        elif section == "cert" and res["cert"] is not None:
            mm = re.search(r"rewrite steps: (\d+) \| verified: (\d+) \| too few valid samples: (\d+) \| FAILED: (\d+)", line)
            if mm: res["cert"].update(dict(zip(["steps", "verified", "sparse", "failed"], map(int, mm.groups()))))
            mm = re.search(r"conditional steps: (\d+) \| guard proven necessary by a counterexample: (\d+)", line)
            if mm: res["cert"].update(dict(zip(["conditional", "witnessed"], map(int, mm.groups()))))
            if line.startswith("    "): res["cert"]["notes"].append(line.strip())
        elif section == "verify" and line.startswith("  "):
            mm = re.match(r"^\s+(\S+)\s+(\d+) points \| mismatches: (\d+) \| fallbacks used: (\d+) \| ill-conditioned skipped: (\d+)(?: \| e\.g\. (.*))?", line)
            if mm: res["verify"].append({"name": mm.group(1), "points": int(mm.group(2)), "mismatches": int(mm.group(3)),
                                         "fallbacks": int(mm.group(4)), "skipped": int(mm.group(5)), "example": mm.group(6) or ""})
        elif section == "bench" and line.startswith("  "):
            mm = re.match(r"^\s+(\S+)\s+tree-walk\s+([\d.]+) \| VM\(original\)\s+([\d.]+) \| VM\(compiled\+guards\)\s+([\d.]+) \| speed-up vs tree-walk ([\d.]+)x", line)
            if mm: res["bench"].append({"name": mm.group(1), "tree": float(mm.group(2)), "vm": float(mm.group(3)), "fast": float(mm.group(4)), "speedup": float(mm.group(5))})
    return res

def run_compile(req):
    src = str(req.get("source", ""))
    if len(src) > MAX_SOURCE: return {"error": "Program is too long (limit %d characters)." % MAX_SOURCE}
    if not os.path.exists(BIN): return {"error": "bin/mathcc not found. Run `make` in the project folder first."}
    mode = req.get("mode", "guarded")
    if mode not in ("guarded", "conservative", "unsafe"): mode = "guarded"
    args = [BIN, "-", "--mode", mode, "--tac", "--why"]
    if req.get("stable"): args.append("--stable")
    if req.get("cert"): args.append("--cert")
    point = str(req.get("point", "")).strip()
    if point:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*=-?[0-9.eE+-]+(,[A-Za-z_][A-Za-z0-9_]*=-?[0-9.eE+-]+)*", point):
            return {"error": "Test point must look like x=2,y=0.5"}
        args += ["--set", point]
    verify = max(0, min(int(req.get("verify") or 0), 200000))
    if verify: args += ["--verify", str(verify)]
    bench = max(0, min(int(req.get("bench") or 0), 5000000))
    if bench: args += ["--bench", str(bench)]
    with tempfile.TemporaryDirectory() as td:
        cpath = os.path.join(td, "out.c")
        args += ["--emit-c", cpath]
        try:
            p = subprocess.run(args, input=src, capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            return {"error": "The compiler took longer than 60 seconds. Try fewer benchmark iterations."}
        if p.returncode != 0:
            return {"error": (p.stderr.strip() or p.stdout.strip() or "compiler failed").replace("error: ", "", 1)}
        res = parse_compile(p.stdout)
        res["mode"] = mode
        res["c"] = open(cpath).read() if os.path.exists(cpath) else ""
        res["raw"] = p.stdout
    return res

def run_discover():
    p = subprocess.run([BIN, "--discover"], capture_output=True, text=True, timeout=60)
    rules, head = [], []
    for line in p.stdout.splitlines():
        m = re.match(r"^\s+(.+?)\s+-> (.+?)\s+\[(.+?)\]\s+(verified|UNVERIFIED)$", line)
        if m: rules.append({"lhs": m.group(1).strip(), "rhs": m.group(2).strip(), "cond": m.group(3), "verified": m.group(4) == "verified"})
        elif not line.startswith("new rules"): head.append(line)
    return {"summary": head, "rules": rules}

class H(BaseHTTPRequestHandler):
    def log_message(self, *a): pass
    def send(self, code, body, ctype="application/json"):
        b = body if isinstance(body, bytes) else body.encode()
        self.send_response(code); self.send_header("Content-Type", ctype); self.send_header("Content-Length", str(len(b)))
        self.send_header("Cache-Control", "no-store"); self.end_headers(); self.wfile.write(b)
    def do_GET(self):
        path = self.path.split("?")[0]
        if path in ("/", "/index.html"):
            return self.send(200, open(os.path.join(STATIC, "index.html"), "rb").read(), "text/html; charset=utf-8")
        if path == "/api/examples":
            out = []
            for f in sorted(os.listdir(EXAMPLES)):
                if f.endswith(".mc"): out.append({"name": f[:-3], "source": open(os.path.join(EXAMPLES, f)).read()})
            return self.send(200, json.dumps(out))
        if path == "/api/discover":
            try: return self.send(200, json.dumps(run_discover()))
            except Exception as e: return self.send(500, json.dumps({"error": str(e)}))
        self.send(404, json.dumps({"error": "not found"}))
    def do_POST(self):
        if self.path != "/api/compile": return self.send(404, json.dumps({"error": "not found"}))
        try:
            n = int(self.headers.get("Content-Length", 0))
            req = json.loads(self.rfile.read(min(n, 200000)) or b"{}")
            self.send(200, json.dumps(run_compile(req)))
        except Exception as e:
            self.send(400, json.dumps({"error": "Bad request: %s" % e}))

if __name__ == "__main__":
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    srv = ThreadingHTTPServer(("127.0.0.1", port), H)
    print("mathcc workbench: http://127.0.0.1:%d   (Ctrl+C to stop)" % port)
    try: srv.serve_forever()
    except KeyboardInterrupt: pass
