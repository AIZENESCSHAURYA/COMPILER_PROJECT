// mathcc - guarded symbolic-simplification compiler for mathematical expressions
#include "frontend.hpp"
#include "analysis.hpp"

static void usage() {
  puts("usage: mathcc <file|-> [options]\n"
       "  --mode guarded|conservative|unsafe   rewrite policy (default guarded)\n"
       "  --set x=1,y=2     evaluate every output at this point (original vs compiled)\n"
       "  --stable          also try numerically stable rewrites, keep the more accurate form\n"
       "  --tac             print three-address code of the compiled outputs\n"
       "  --why             explain every rewrite step (rule, guards, skipped rewrites)\n"
       "  --cert            check every rewrite step with the independent certificate checker\n"
       "  --verify N        compare compiled vs original on N random points\n"
       "  --bench N         time N evaluations: naive tree-walk / VM(original) / VM(compiled)\n"
       "  --emit-c FILE     write C source (fast path + guarded fallback)\n"
       "  --c-stdout        print the C source after the report (used by the web page)\n"
       "  --tokens          dump the token stream\n"
       "  --discover        rule discovery: find new identities with inferred side conditions");
}

int main(int argc, char** argv) {
  string file, setArg, cfile; Mode mode = M_GUARDED;
  bool why = false, cstdout = false, stable = false, tac = false, cert = false, tokens = false, discover = false; int verifyN = 0; long benchN = 0;
  for (int i = 1; i < argc; i++) {
    string a = argv[i];
    auto next = [&]() -> string { if (i + 1 >= argc) { usage(); exit(2); } return argv[++i]; };
    if (a == "--mode") { string m = next(); mode = m == "unsafe" ? M_UNSAFE : m == "conservative" ? M_CONSERVATIVE : M_GUARDED; }
    else if (a == "--set") setArg = next();
    else if (a == "--stable") stable = true;
    else if (a == "--tac") tac = true;
    else if (a == "--why") why = true;
    else if (a == "--cert") cert = true;
    else if (a == "--verify") verifyN = atoi(next().c_str());
    else if (a == "--bench") benchN = atol(next().c_str());
    else if (a == "--emit-c") cfile = next();
    else if (a == "--c-stdout") cstdout = true;
    else if (a == "--tokens") tokens = true;
    else if (a == "--discover") discover = true;
    else if (a == "-h" || a == "--help") { usage(); return 0; }
    else file = a;
  }
  if (discover) {
    int nExprs = 0, nKnown = 0, nAbs = 0;
    auto rules = discoverRules(nExprs, nKnown, nAbs);
    printf("enumerated %d expressions in x; %d identities already known to the simplifier were skipped\n", nExprs, nKnown);
    printf("%d sign-resolution rules for abs() omitted (already handled by interval analysis)\n", nAbs);
    printf("new rules (lhs -> rhs, side condition inferred from the region where they agree):\n");
    for (auto& r : rules) printf("  %-28s -> %-18s [%s]%s\n", r.lhs.c_str(), r.rhs.c_str(), r.cond.c_str(), r.verified ? "  verified" : "  UNVERIFIED");
    return 0;
  }
  if (file.empty()) { usage(); return 2; }
  string src;
  { stringstream ss; if (file == "-") ss << cin.rdbuf(); else { ifstream f(file); if (!f) { fprintf(stderr, "cannot open %s\n", file.c_str()); return 2; } ss << f.rdbuf(); } src = ss.str(); }

  Arena A; Parser P(A);
#ifndef MATHCC_NO_EXCEPTIONS
  try {
#endif
    if (tokens) {
      stringstream ss(src); string l; int n = 0;
      while (getline(ss, l)) { n++; auto t = lexLine(l, n); if (t.size() == 1) continue;
        printf("line %d:", n); for (auto& k : t) if (k.k != Tok::END) printf(" %s%s", k.k == Tok::NUM ? "NUM:" : k.k == Tok::ID ? "ID:" : "", k.s.c_str()); puts(""); }
      puts("");
    }
    P.parse(src);
#ifndef MATHCC_NO_EXCEPTIONS
  } catch (CompileError& e) { fprintf(stderr, "error: %s\n", e.what()); return 1; }
#endif

  vector<string>& vn = A.varNames;
  printf("mathcc | mode=%s | inputs:", mode == M_GUARDED ? "guarded" : mode == M_CONSERVATIVE ? "conservative" : "UNSAFE");
  for (size_t i = 0; i < vn.size(); i++) {
    const Iv& v = A.varIv[i]; printf(" %s", vn[i].c_str());
    if (v.lo > -INF || v.hi < INF || v.nz) { printf("("); if (v.lo > -INF) printf("%s%g", v.lo == 0 && v.nz ? ">" : ">=", v.lo); if (v.lo > -INF && v.hi < INF) printf(","); if (v.hi < INF) printf("%s%g", v.hi == 0 && v.nz ? "<" : "<=", v.hi); if (v.nz && v.lo <= -INF && v.hi >= INF) printf("!=0"); printf(")"); }
  }
  puts("\n");

  vector<Compiled> compiled; vector<Step> allSteps; vector<string> cOut;
  for (auto& o : P.outs) {
    Simplifier S1(A, mode); int simp = S1.S(o.raw);
    Compiled c = compileOutput(A, o.name, o.raw, simp, S1.guards);
    vector<Step> steps = S1.steps; vector<string> refusedSteps = S1.refused; int nProven = S1.nProven, nRuntime = S1.nRuntime, nRefused = S1.nRefused;
    string stabNote;
    if (stable) {
      Simplifier S2(A, mode); int raw2 = S2.stab(o.raw);
      if (raw2 != o.raw) {
        int simp2 = S2.S(raw2);
        Compiled c2 = compileOutput(A, o.name, o.raw, simp2, S2.guards);
        double e1 = measuredError(A, c, 600, 7), e2 = measuredError(A, c2, 600, 7);
        double k1 = costOf(c.fast), k2 = costOf(c2.fast);
        char buf[300]; snprintf(buf, sizeof buf, "stability: candidate A max rel.err %.2e cost %.0f | stable form [%s] max rel.err %.2e cost %.0f", e1, k1, show(A, simp2).c_str(), e2, k2);
        stabNote = buf;
        if (e2 < e1 / 4 && k2 <= 2 * k1 + 10) {
          stabNote += "  => stable form selected";
          c = c2; simp = simp2; steps = S2.steps; refusedSteps = S2.refused; nProven = S2.nProven; nRuntime = S2.nRuntime; nRefused = S2.nRefused;
        } else stabNote += "  => kept candidate A";
      } else stabNote = "stability: no stable rewrite applies";
    }
    printf("[%s]\n  original  : %s\n  simplified: %s\n", o.name.c_str(), show(A, o.raw).c_str(), show(A, simp).c_str());
    if (c.guards.empty()) printf("  guards    : none at run time (%d side condition(s) proven from assumptions%s)\n", nProven, nRefused ? ", some rewrites skipped" : "");
    else {
      printf("  guards    : %zu runtime check(s); falls back to the original expression if one fails\n", c.guards.size());
      for (auto& g : c.guards) printf("              - %s\n", guardStr(A, g).c_str());
      if (nProven) printf("              (%d more proven statically)\n", nProven);
    }
    if (nRefused) printf("  skipped   : %d rewrite(s) refused (condition false or not allowed in this mode)\n", nRefused);
    printf("  size      : DAG %d -> %d nodes ; VM %zu -> %zu instructions\n", countNodes(A, o.raw), countNodes(A, simp), c.orig.code.size(), c.fast.code.size());
    if (!stabNote.empty()) printf("  %s\n", stabNote.c_str());
    if (why) {
      puts("  why:");
      set<string> seenStep;
      for (auto& st : steps) {
        string a = show(A, st.pre), b = show(A, st.post);
        if (a == b) continue;                                   // pure re-ordering, nothing to explain
        string line = "    step|" + st.rule + "|" + a + "|" + b + "|";
        for (size_t g = 0; g < st.gs.size(); g++) line += (g ? ";" : "") + guardStr(A, st.gs[g]) + "~" + (st.proven[g] == 1 ? "P" : st.proven[g] == 2 ? "I" : "R");
        if (seenStep.insert(line).second) puts(line.c_str());
      }
      set<string> seenSkip;
      for (auto& r : refusedSteps) if (seenSkip.insert(r).second) printf("    skip|%s\n", r.c_str());
    }
    if (tac) { puts("  three-address code (fast path):"); for (auto& i : c.fast.code) printf("    %s\n", tacStr(i, vn).c_str());
      printf("    result = t%d\n", c.fast.outs[0]); for (size_t g = 0; g < c.guards.size(); g++) printf("    guard %zu: %s  (value t%d)\n", g, guardStr(A, c.guards[g]).c_str(), c.fast.outs[g + 1]); }
    puts("");
    allSteps.insert(allSteps.end(), steps.begin(), steps.end());
    cOut.push_back(emitC(c, vn));
    compiled.push_back(move(c));
  }

  if (!setArg.empty()) {
    vector<double> x(vn.size(), 0); vector<bool> got(vn.size(), false);
    stringstream ss(setArg); string kv;
    while (getline(ss, kv, ',')) { auto eq = kv.find('='); if (eq == string::npos) { fprintf(stderr, "bad --set item '%s'\n", kv.c_str()); return 2; }
      string k = kv.substr(0, eq); bool f = false;
      for (size_t i = 0; i < vn.size(); i++) if (vn[i] == k) { x[i] = strtod(kv.c_str() + eq + 1, nullptr); got[i] = f = true; }
      if (!f) { fprintf(stderr, "unknown variable '%s'\n", k.c_str()); return 2; } }
    for (size_t i = 0; i < vn.size(); i++) if (!got[i]) { fprintf(stderr, "--set is missing a value for '%s'\n", vn[i].c_str()); return 2; }
    puts("evaluation:");
    for (auto& c : compiled) {
      vector<double> regs(max(c.fast.nregs, c.orig.nregs) + 1); bool fb = false;
      double v = evalCompiled(c, x.data(), regs.data(), &fb);
      printf("  %-6s original = %-14s compiled = %-14s%s\n", c.name.c_str(), fmtNum(evalTree(A, c.raw, x.data())).c_str(), fmtNum(v).c_str(), fb ? "  (runtime guard failed -> fallback used)" : "");
    }
    puts("");
  }

  if (cert) {
    puts("certificate check (independent sampler; every step must hold wherever its guards hold):");
    CertReport R = certify(A, allSteps, 99);
    printf("  rewrite steps: %d | verified: %d | too few valid samples: %d | FAILED: %d\n", R.steps, R.verified, R.sparse, R.failed);
    printf("  conditional steps: %d | guard proven necessary by a counterexample: %d\n", R.conditional, R.witnessed);
    for (auto& n : R.notes) printf("    %s\n", n.c_str());
    puts("");
  }
  if (verifyN > 0) {
    puts("end-to-end verification (compiled vs original expression, NaN-aware):");
    long bad = 0;
    for (auto& c : compiled) {
      VerifyReport v = verifyOutput(A, c, verifyN, 2024); bad += v.mismatch;
      printf("  %-6s %ld points | mismatches: %ld | fallbacks used: %ld | ill-conditioned skipped: %ld%s%s\n", c.name.c_str(), v.n, v.mismatch, v.fallback, v.skipped, v.first.empty() ? "" : " | e.g. ", v.first.c_str());
    }
    puts("");
  }
  if (benchN > 0) {
    puts("benchmark (ns per evaluation, lower is better):");
    Sampler S(5); const int M = 1024; vector<vector<double>> pts;
    for (int i = 0; i < M; i++) pts.push_back(S.point(A, false));
    for (auto& c : compiled) {
      vector<double> regs(max(c.fast.nregs, c.orig.nregs) + 1); volatile double sink = 0;
      auto t0 = chrono::steady_clock::now();
      for (long i = 0; i < benchN; i++) sink = evalTree(A, c.raw, pts[i % M].data());
      auto t1 = chrono::steady_clock::now();
      for (long i = 0; i < benchN; i++) { runProg(c.orig, pts[i % M].data(), regs.data()); sink = regs[c.orig.outs[0]]; }
      auto t2 = chrono::steady_clock::now();
      for (long i = 0; i < benchN; i++) sink = evalCompiled(c, pts[i % M].data(), regs.data());
      auto t3 = chrono::steady_clock::now();
      double a = chrono::duration<double, nano>(t1 - t0).count() / benchN, b = chrono::duration<double, nano>(t2 - t1).count() / benchN, d = chrono::duration<double, nano>(t3 - t2).count() / benchN;
      printf("  %-6s tree-walk %8.1f | VM(original) %8.1f | VM(compiled+guards) %8.1f | speed-up vs tree-walk %.1fx\n", c.name.c_str(), a, b, d, a / d);
      (void)sink;
    }
    puts("");
  }
  if (cstdout) {
    puts("----C----");
    puts("/* generated by mathcc: fast path + guarded fallback. cc -O2 file.c -lm */\n#include <math.h>\n");
    for (auto& s : cOut) printf("%s\n", s.c_str());
  }
  if (!cfile.empty()) {
    ofstream f(cfile); f << "/* generated by mathcc: fast path + guarded fallback. cc -O2 file.c -lm */\n#include <math.h>\n\n";
    for (auto& s : cOut) f << s << "\n";
    printf("wrote %s\n", cfile.c_str());
  }
  return 0;
}
