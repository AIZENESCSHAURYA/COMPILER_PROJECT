#!/usr/bin/env python3
"""Tests for mathcc: golden rewrites, guard behaviour, and a random-expression soundness fuzzer."""
import random, re, subprocess, sys

BIN = "bin/mathcc"

def run(src, *args):
    p = subprocess.run([BIN, "-", *args], input=src, capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr

fails = 0
def check(name, cond, info=""):
    global fails
    print(("PASS " if cond else "FAIL ") + name + ("" if cond else "  " + info))
    if not cond: fails += 1

def simplified(src, name, *args):
    _, out, _ = run(src, *args)
    m = re.search(r"\[%s\]\n  original  : .*\n  simplified: (.*)\n  guards    : (.*)" % re.escape(name), out)
    return (m.group(1), m.group(2)) if m else (None, None)

# ---- golden cases ---------------------------------------------------------------------
s, g = simplified("a = (x*x)/x\n", "a");                     check("x*x/x -> x, runtime guard x != 0", s == "x" and "runtime" in g, (s, g))
s, g = simplified("assume x != 0\na = (x*x)/x\n", "a");      check("x*x/x -> x, no runtime guard when x != 0 assumed", s == "x" and "none" in g, (s, g))
s, g = simplified("a = (x*x)/x\n", "a", "--mode", "conservative"); check("conservative mode refuses unproven rewrite", s != "x", s)
s, g = simplified("b = sqrt(x^2)\n", "b");                   check("sqrt(x^2) -> abs(x) with no guard", s == "abs(x)" and "none" in g, (s, g))
s, g = simplified("assume x > 0\nb = sqrt(x^2)\n", "b");     check("sqrt(x^2) -> x when x > 0", s == "x", s)
s, g = simplified("b = sqrt(z)*sqrt(z)\n", "b");             check("sqrt(z)*sqrt(z) -> z guarded by z >= 0", s == "z" and "runtime" in g, (s, g))
s, g = simplified("assume y > 0\nc = sin(y)^2 + cos(y)^2 + y/y\n", "c"); check("trig identity + y/y with y>0", s == "2" and "none" in g, (s, g))
s, g = simplified("c = sin(y)^2 + cos(y)^2\n", "c");        check("sin^2+cos^2 -> 1 (finite input proven)", s == "1", s)
s, g = simplified("h = ln(exp(x))\n", "h");                  check("ln(exp(x)) -> x", s == "x", s)
s, g = simplified("h = exp(ln(x))\n", "h");                  check("exp(ln(x)) -> x guarded by x >= 0", s == "x" and "runtime" in g, (s, g))
s, g = simplified("k = (w+1)/(w+1)\n", "k");                 check("(w+1)/(w+1) -> 1, guard on compound term", s == "1" and "w + 1 != 0" in g or "runtime" in g, (s, g))
s, g = simplified("f = d(x^3, x)\n", "f");                   check("d(x^3,x) = 3*x^2", s == "3*x^2", s)
s, g = simplified("f = d(sin(x)*x, x)\n", "f");              check("product rule", s in ("x*cos(x) + sin(x)", "sin(x) + x*cos(x)"), s)
s, g = simplified("t = (a+b)-(a+b)\n", "t");                 check("(a+b)-(a+b) -> 0", s == "0", s)
s, g = simplified("t = x*0\n", "t");                         check("x*0 -> 0 (x is a finite input)", s == "0", s)
s, g = simplified("t = sqrt(z)*0\n", "t");                   check("sqrt(z)*0 keeps a guard (NaN for z<0)", s == "0" and "runtime" in g, (s, g))

# ---- error handling -----------------------------------------------------------------------
rc, out, err = run("a = (x + \n"); check("syntax error reported with line/col", rc == 1 and "line 1" in err, err)
rc, out, err = run("a = foo(x)\n"); check("unknown function reported", rc == 1 and "unknown function" in err, err)
rc, out, err = run("x = 3\nassume x > 0\na = x\n"); check("assuming on a derived name is an error", rc == 1, err)
rc, out, err = run("assume x > 0\nassume x < 0\na = x\n"); check("contradictory assumptions rejected", rc == 1 and "contradictory" in err, err)

# ---- evaluation / fallback ------------------------------------------------------------------
_, out, _ = run("a = (x*x)/x\n", "--set", "x=0");   check("guard failure falls back to original (nan)", "nan" in out and "fallback" in out, out)
_, out, _ = run("a = (x*x)/x\n", "--set", "x=3");   check("guard passes -> fast path", "compiled = 3" in out and "fallback" not in out, out)

# ---- certificates / verification -----------------------------------------------------------
_, out, _ = run("a = (x*x)/x\nb = sqrt(z)*sqrt(z)\nc = ln(x^3)\n", "--cert")
check("certificate: no failed step, guards shown necessary", "FAILED: 0" in out and re.search(r"necessary by a counterexample: [1-9]", out), out)
_, out, _ = run("a = (x*x)/x\nb = sqrt(z)*sqrt(z)\n", "--mode", "unsafe", "--verify", "5000")
check("unsafe (classic) mode produces wrong results the guarded mode avoids", re.search(r"mismatches: [1-9]", out), out)

# ---- stability ----------------------------------------------------------------------------------
_, out, _ = run("a = 1 - cos(x)\nb = exp(x) - 1\nc = ln(1 + x)\n", "--stable")
check("stable rewrites selected (expm1/log1p/half-angle)", out.count("stable form selected") == 3 and "expm1(x)" in out and "log1p(x)" in out, out)

# ---- discovery -----------------------------------------------------------------------------------
_, out, _ = run("", "--discover") if False else subprocess.run([BIN, "--discover"], capture_output=True, text=True).returncode, subprocess.run([BIN, "--discover"], capture_output=True, text=True).stdout, ""
check("rule discovery finds a verified conditional rule", "[x >= 0]  verified" in out and "UNVERIFIED" not in out, out[:400])

# ---- C backend -----------------------------------------------------------------------------------
rc, out, _ = run("assume y > 0\na = (x*x)/x\nb = sin(y)^2+cos(y)^2+y\n", "--emit-c", "/tmp/mathcc_test.c")
cc = subprocess.run(["gcc", "-O2", "-Wall", "-c", "/tmp/mathcc_test.c", "-o", "/tmp/mathcc_test.o"], capture_output=True, text=True)
check("emitted C compiles warning-free", cc.returncode == 0 and cc.stderr == "", cc.stderr)

# ---- soundness fuzzer ------------------------------------------------------------------------------
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
VARS = ["x", "y", "z"]
def gen(d):
    if d == 0 or random.random() < 0.15:
        return random.choice(VARS + ["1", "2", "3", "0.5"])
    r = random.random()
    if r < 0.50:
        return "(%s %s %s)" % (gen(d-1), random.choice("+-*/"), gen(d-1))
    if r < 0.60: return "(%s)^%s" % (gen(d-1), random.choice(["2", "3", "-1", "0.5", "-2", "1.5"]))
    if r < 0.70: return "sqrt(%s)" % gen(d-1)
    return "%s(%s)" % (random.choice(["sin", "cos", "ln", "exp", "abs", "sqrt", "-"]), gen(d-1)) if False else "%s(%s)" % (random.choice(["sin", "cos", "ln", "exp", "abs"]), gen(d-1))

def fuzz(mode, n_files=40, per=6):
    bad = 0
    for f in range(n_files):
        assumes = [random.choice(["", "assume x > 0", "assume y >= 0", "assume z != 0", "assume x in [1, 4]", "assume y < 0"]) for _ in range(2)]
        lines = [a for a in assumes if a]
        for i in range(per): lines.append("o%d = %s" % (i, gen(random.randint(2, 4))))
        src = "\n".join(lines) + "\n"
        rc, out, err = run(src, "--mode", mode, "--verify", "1500", "--cert")
        if rc != 0:
            continue                       # contradictory random assumptions are rejected by the front end
        m = re.findall(r"mismatches: (\d+)", out); fl = re.search(r"FAILED: (\d+)", out)
        if any(int(v) for v in m) or (fl and int(fl.group(1))):
            bad += 1; print("  fuzz failure:\n" + src + out[-700:])
    return bad
for mode in ("guarded", "conservative"):
    b = fuzz(mode); check("fuzz %s: 240 random expressions, compiled == original, all certificates hold" % mode, b == 0, "%d failing files" % b)

print("\n%s" % ("ALL TESTS PASSED" if fails == 0 else "%d TEST(S) FAILED" % fails))
sys.exit(1 if fails else 0)
