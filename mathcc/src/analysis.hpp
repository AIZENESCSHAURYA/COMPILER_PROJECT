// analysis.hpp - independent certificate checker, end-to-end verifier, accuracy measurement, rule discovery
#pragma once
#include "backend.hpp"

struct Sampler {
  mt19937_64 rng;
  explicit Sampler(uint64_t s) : rng(s) {}
  double u01() { return uniform_real_distribution<double>(0, 1)(rng); }
  static bool ok(const Iv& v, double c) { return c >= v.lo && c <= v.hi && !(v.nz && c == 0); }
  double one(const Iv& v, bool edge) {
    static const double cands[] = {0, 1, -1, 2, -2, 0.5, -0.5, 3, -3, 0.1, -0.1, 10, -10};
    if (edge && u01() < 0.5) { double c = cands[rng() % 13]; if (ok(v, c)) return c; }
    double lo = max(v.lo, -8.0), hi = min(v.hi, 8.0);
    if (v.lo > 8) { lo = v.lo; hi = v.lo + 8; } else if (v.hi < -8) { hi = v.hi; lo = v.hi - 8; }
    for (int k = 0; k < 60; k++) { double c = lo + (hi - lo) * u01(); if (ok(v, c)) return c; }
    return (lo + hi) / 2;
  }
  vector<double> point(const Arena& A, bool edge) {
    vector<double> x(A.varNames.size());
    for (size_t i = 0; i < x.size(); i++) x[i] = one(A.varIv[i], edge);
    return x;
  }
  // log-uniform magnitudes: exposes cancellation / overflow-ish behaviour
  vector<double> pointLog(const Arena& A) {
    vector<double> x(A.varNames.size());
    for (size_t i = 0; i < x.size(); i++) {
      for (int k = 0; k < 100; k++) {
        double m = pow(10.0, -6 + 8 * u01()), c = (u01() < 0.5 ? -m : m);
        if (ok(A.varIv[i], c)) { x[i] = c; goto next; }
        if (ok(A.varIv[i], -c)) { x[i] = -c; goto next; }
      }
      x[i] = one(A.varIv[i], false);
      next:;
    }
    return x;
  }
};

inline bool sameVal(double a, double b, double tol = 1e-9) {
  if (isnan(a) && isnan(b)) return true;
  if (isnan(a) || isnan(b)) return isinf(a) || isinf(b);   // NaN vs +-inf: a domain-boundary rounding effect (ln(0) vs ln(-1e-16)), not a semantic difference
  if (isinf(a) || isinf(b)) return isinf(a) && isinf(b);   // +-0 are identified, so the sign of an infinity is not compared
  return fabs(a - b) <= tol * max(1.0, max(fabs(a), fabs(b)));
}

// ---------------------------------------------------------------------------------
// Certificate checker.  It trusts nothing from the simplifier except the recorded
// steps (pre, post, guards).  For every step it samples inputs that satisfy the
// assumptions AND the step's guards and checks pre == post (NaN-aware).  It also
// looks for a counterexample with the guards switched off, showing each runtime
// guard is necessary and not decoration.
// ---------------------------------------------------------------------------------
struct CertReport {
  int steps = 0, verified = 0, sparse = 0, failed = 0, conditional = 0, witnessed = 0;
  vector<string> notes;
};
inline CertReport certify(const Arena& A, const vector<Step>& steps, uint64_t seed, int tries = 3000) {
  CertReport R; Sampler S(seed);
  set<pair<int, int>> seen;
  for (const Step& st : steps) {
    if (!seen.insert({st.pre, st.post}).second) continue;
    R.steps++;
    int accepted = 0; bool bad = false, anyGuardFail = false, witness = false; string wnote, fnote;
    for (int t = 0; t < tries; t++) {
      vector<double> x = S.point(A, true);
      bool all = true; int failedGuard = -1;
      for (size_t g = 0; g < st.gs.size(); g++)
        if (!guardHolds(st.gs[g].k, evalTree(A, st.gs[g].node, x.data()))) { all = false; failedGuard = (int)g; break; }
      double a = evalTree(A, st.pre, x.data()), b = evalTree(A, st.post, x.data());
      bool same = sameVal(a, b);
      if (all) { accepted++; if (!same && !bad) { bad = true; fnote = "FAILS at " + show(A, st.pre) + " vs " + show(A, st.post); } }
      else {
        anyGuardFail = true;
        if (!same && !witness) {
          witness = true; char buf[200];
          string xs; for (size_t i = 0; i < x.size(); i++) xs += (i ? "," : "") + A.varNames[i] + "=" + fmtNum(x[i]);
          snprintf(buf, sizeof buf, "guard [%s] dropped -> [%s] gives %s but original gives %s", guardStr(A, st.gs[failedGuard]).c_str(), xs.c_str(), fmtNum(b).c_str(), fmtNum(a).c_str());
          wnote = buf;
        }
      }
    }
    if (bad) { R.failed++; R.notes.push_back(fnote); }
    else if (accepted < 30) R.sparse++;
    else R.verified++;
    if (anyGuardFail) { R.conditional++; if (witness) { R.witnessed++; if (R.notes.size() < 6) R.notes.push_back("witness: " + wnote); } }
  }
  return R;
}

// ---- end-to-end verification of compiled outputs against the original expression ----
struct VerifyReport { long n = 0, mismatch = 0, fallback = 0, skipped = 0; string first; };
inline VerifyReport verifyOutput(const Arena& A, const Compiled& c, int N, uint64_t seed) {
  VerifyReport R; Sampler S(seed);
  vector<double> regs(max(c.fast.nregs, c.orig.nregs) + 1);
  for (int i = 0; i < N; i++) {
    vector<double> x = S.point(A, i % 5 < 2);
    double truth = evalTree(A, c.raw, x.data()); bool fb = false;
    // Equivalent forms may differ by a few ulps; where the ORIGINAL expression is itself unstable under a
    // 1e-10 relative input perturbation (cos(exp(30)), catastrophic cancellation) a comparison is meaningless.
    // Perturbation is multiplicative, so exact zeros stay zero and edge cases are still tested.
    // Points where the original is NaN/inf are NOT skipped: that is exactly where guards matter.
    bool unstable = false;
    for (int pat = 0; isfinite(truth) && pat < 3; pat++) {        // each coordinate is perturbed independently (ratios z/y change too)
      vector<double> xp = x;
      for (size_t k = 0; k < xp.size(); k++) xp[k] *= 1 + 1e-10 * (pat == 0 ? (double)(k + 1) : pat == 1 ? -(double)(k + 1) : (double)(xp.size() - k));
      if (!sameVal(truth, evalTree(A, c.raw, xp.data()), 1e-6)) unstable = true;
    }
    if (unstable) { R.skipped++; continue; }
    double got = evalCompiled(c, x.data(), regs.data(), &fb);
    R.n++; if (fb) R.fallback++;
    if (!sameVal(truth, got, 1e-6)) {
      R.mismatch++;
      if (R.first.empty()) {
        string xs; for (size_t k = 0; k < x.size(); k++) xs += (k ? "," : "") + A.varNames[k] + "=" + fmtNum(x[k]);
        R.first = xs + "  original=" + fmtNum(truth) + "  compiled=" + fmtNum(got);
      }
    }
  }
  return R;
}

// ---- cost model and measured accuracy ----------------------------------------------
inline double costOf(const Prog& P) {
  double c = 0;
  for (auto& i : P.code) switch (i.op) {
    case V_CONST: case V_VAR: break;
    case V_ADD: case V_SUB: case V_MUL: case V_NEG: case V_ABS: c += 1; break;
    case V_DIV: c += 4; break;
    case V_SQRT: c += 5; break;
    default: c += 20;
  }
  return c;
}
// max relative error of the compiled output versus the ORIGINAL expression evaluated in
// long double (64-bit mantissa), over log-uniform magnitudes.
inline double measuredError(const Arena& A, const Compiled& c, int N, uint64_t seed) {
  Sampler S(seed); vector<double> regs(max(c.fast.nregs, c.orig.nregs) + 1); double worst = 0;
  for (int i = 0; i < N; i++) {
    vector<double> x = S.pointLog(A);
    long double truth = evalTreeT<long double>(A, c.raw, x.data());
    if (!isfinite((double)truth) || fabsl(truth) < 1e-300L) continue;
    double got = evalCompiled(c, x.data(), regs.data());
    if (isnan(got)) { worst = max(worst, 1.0); continue; }
    double rel = (double)(fabsl((long double)got - truth) / fabsl(truth));
    worst = max(worst, rel);
  }
  return worst;
}

// ---------------------------------------------------------------------------------
// Rule discovery: enumerate small expressions in x, group by behaviour on sample
// points restricted to a region (all / x!=0 / x>=0 / x>0 / x<0), and report pairs that
// agree on a region but that the simplifier does not already identify.  The region is
// the inferred side condition.  Every candidate is re-tested on fresh random points.
// ---------------------------------------------------------------------------------
struct DiscoveredRule { string lhs, rhs, cond; bool verified; int size; };

inline vector<DiscoveredRule> discoverRules(int& nExprs, int& nKnown, int& nAbs, int limit = 40) {
  nAbs = 0;
  Arena A; A.newVar("x");
  int X = A.var(0), one = A.num(1), two = A.num(2);
  vector<int> E0{X, one, two}, all;
  auto expand = [&](const vector<int>& base) {
    set<int> out(base.begin(), base.end());
    for (int e : base) {
      out.insert(A.mk(NEG, e)); out.insert(A.mk(SQRT, e)); out.insert(A.mk(ABS, e));
      out.insert(A.mk(LN, e)); out.insert(A.mk(EXP, e)); out.insert(A.mk(SIN, e)); out.insert(A.mk(COS, e));
      out.insert(A.mk(POW, e, two)); out.insert(A.mk(POW, e, A.num(-1)));
    }
    for (int a : base) for (int b : base) {
      out.insert(A.mk(ADD, a, b)); out.insert(A.mk(SUB, a, b));
      out.insert(A.mk(MUL, a, b)); out.insert(A.mk(DIV, a, b));
    }
    return vector<int>(out.begin(), out.end());
  };
  vector<int> E1 = expand(E0);
  { set<int> out(E1.begin(), E1.end());
    for (int e : E1) {
      out.insert(A.mk(SQRT, e)); out.insert(A.mk(ABS, e)); out.insert(A.mk(LN, e)); out.insert(A.mk(EXP, e));
      out.insert(A.mk(POW, e, two)); out.insert(A.mk(POW, e, A.num(-1))); out.insert(A.mk(NEG, e));
    }
    // binary combinations of a small base set with level-1 expressions
    for (int a : E0) for (int b : E1) {
      out.insert(A.mk(ADD, a, b)); out.insert(A.mk(SUB, a, b)); out.insert(A.mk(SUB, b, a));
      out.insert(A.mk(MUL, a, b)); out.insert(A.mk(DIV, a, b)); out.insert(A.mk(DIV, b, a));
    }
    for (int a : E1) for (int b : E1) {          // two-level combinations
      out.insert(A.mk(ADD, a, b)); out.insert(A.mk(SUB, a, b)); out.insert(A.mk(MUL, a, b)); out.insert(A.mk(DIV, a, b));
    }
    all.assign(out.begin(), out.end()); }
  nExprs = (int)all.size();

  vector<double> xs = {-5, -3, -2, -1.5, -1, -0.7, -0.5, -0.25, -0.1, 0, 0.1, 0.25, 0.5, 0.7, 1, 1.5, 2, 3, 5, 0.3, -0.3, 4, -4, 2.5};
  enum { R_ALL, R_NZ, R_NONNEG, R_POS, R_NEG, NR };
  const char* rname[NR] = {"always", "x != 0", "x >= 0", "x > 0", "x < 0"};
  auto inRegion = [&](int r, double x) {
    switch (r) { case R_ALL: return true; case R_NZ: return x != 0; case R_NONNEG: return x >= 0; case R_POS: return x > 0; default: return x < 0; }
  };
  auto subset = [&](int small, int big) {          // region small is contained in region big
    if (small == big || big == R_ALL) return true;
    if (big == R_NZ) return small == R_POS || small == R_NEG;
    if (big == R_NONNEG) return small == R_POS;
    return false;
  };
  vector<vector<double>> vals(all.size(), vector<double>(xs.size()));
  vector<char> usesX(all.size());
  for (size_t i = 0; i < all.size(); i++) {
    for (size_t k = 0; k < xs.size(); k++) vals[i][k] = evalTree(A, all[i], &xs[k]);
    unordered_set<int> seen; vector<int> st{all[i]}; bool ux = false;
    while (!st.empty()) { int u = st.back(); st.pop_back(); if (!seen.insert(u).second) continue;
      if (A.n[u].op == VAR) ux = true; if (A.n[u].a >= 0) st.push_back(A.n[u].a); if (A.n[u].b >= 0) st.push_back(A.n[u].b); }
    usesX[i] = ux;
  }
  Simplifier S(A, M_GUARDED);
  vector<int> canon(all.size()), sz(all.size());
  auto wcost = [&](int root) {
    unordered_set<int> seen; vector<int> st{root}; int c = 0;
    while (!st.empty()) {
      int u = st.back(); st.pop_back(); if (!seen.insert(u).second) continue;
      switch (A.n[u].op) { case NUM: case VAR: break; case ADD: case SUB: case MUL: case NEG: case ABS: c += 2; break;
        case DIV: c += 5; break; case SQRT: c += 6; break; case POW: c += 3; break; default: c += 20; }
      if (A.n[u].a >= 0) st.push_back(A.n[u].a); if (A.n[u].b >= 0) st.push_back(A.n[u].b);
    }
    return c; };
  for (size_t i = 0; i < all.size(); i++) { canon[i] = S.S(all[i]); sz[i] = wcost(all[i]); }
  // constant-valued expressions (x - x, exp(0*x), ...) are not interesting rules about x
  vector<char> constant(all.size());
  for (size_t i = 0; i < all.size(); i++) {
    bool c = true; double first = NAN; bool have = false;
    for (double v : vals[i]) { if (isnan(v)) continue; if (!have) { first = v; have = true; } else if (!(v == first)) c = false; }
    constant[i] = c;
  }

  auto fp = [&](size_t i, int r) {
    string key; bool anyReal = false;
    for (size_t k = 0; k < xs.size(); k++) if (inRegion(r, xs[k])) {
      double v = vals[i][k];
      if (isnan(v)) key += "n,"; else if (isinf(v)) key += v > 0 ? "+,": "-,";
      else { key += to_string(llround(v * 1e8)) + ","; anyReal = true; }
    }
    return anyReal ? key : string();
  };
  vector<DiscoveredRule> rules; set<pair<int, int>> done[NR]; nKnown = 0;
  vector<string> fullFp(all.size()); for (size_t i = 0; i < all.size(); i++) fullFp[i] = fp(i, R_ALL);
  Sampler vs(12345);
  for (int r = 0; r < NR; r++) {
    unordered_map<string, vector<size_t>> groups;
    for (size_t i = 0; i < all.size(); i++) if (usesX[i] && !constant[i]) { string k = fp(i, r); if (!k.empty()) groups[k].push_back(i); }
    for (auto& [k, g] : groups) {
      if (g.size() < 2) continue;
      size_t rep = g[0];
      for (size_t i : g) if (sz[i] < sz[rep] || (sz[i] == sz[rep] && all[i] < all[rep])) rep = i;
      for (size_t i : g) {
        if (i == rep || sz[i] <= sz[rep]) continue;
        if (r != R_ALL && fullFp[i] == fullFp[rep]) continue;     // already holds everywhere
        bool skip = false;
        for (int r2 = 0; r2 < NR; r2++) if (r2 != r && subset(r, r2) && done[r2].count({(int)i, (int)rep})) skip = true;
        if (skip) continue;
        done[r].insert({(int)i, (int)rep});
        if (canon[i] == canon[rep]) { nKnown++; continue; }       // simplifier already knows it
        // independent re-test on fresh points inside the region
        Iv reg; reg.def = true;
        if (r == R_NZ) reg.nz = true; if (r == R_NONNEG) reg.lo = 0; if (r == R_POS) { reg.lo = 0; reg.nz = true; } if (r == R_NEG) { reg.hi = 0; reg.nz = true; }
        bool okAll = true;
        for (int t = 0; t < 4000 && okAll; t++) {
          double x = vs.one(reg, true);
          if (!sameVal(evalTree(A, all[i], &x), evalTree(A, all[rep], &x), 1e-9)) okAll = false;
        }
        rules.push_back({show(A, all[i]), show(A, all[rep]), rname[r], okAll, sz[i]});
      }
    }
  }
  sort(rules.begin(), rules.end(), [](const DiscoveredRule& a, const DiscoveredRule& b) {    // total order: output is deterministic
    if (a.verified != b.verified) return a.verified > b.verified;
    if ((a.cond != "always") != (b.cond != "always")) return a.cond != "always";   // conditional rules first
    auto fn = [](const DiscoveredRule& r) { for (const char* f : {"ln(", "exp(", "sqrt(", "sin(", "cos("}) if (r.lhs.find(f) != string::npos) return true; return false; };
    if (fn(a) != fn(b)) return fn(a);                                                // rules about functions before plain arithmetic
    if (a.size != b.size) return a.size < b.size;
    if (a.lhs != b.lhs) return a.lhs < b.lhs;
    if (a.rhs != b.rhs) return a.rhs < b.rhs;
    return a.cond < b.cond; });
  int nc = 0, nu = 0; vector<DiscoveredRule> keep; set<string> dedupe; map<string, int> perRhs;
  for (auto& r : rules) {
    if (!dedupe.insert(r.lhs + "|" + r.rhs + "|" + r.cond).second) continue;
    if (r.cond != "always" && r.lhs.find("abs(") != string::npos) { nAbs++; continue; }   // abs sign-resolution: subsumed by interval analysis
    if (r.cond != "always" && r.rhs.find("abs(") != string::npos) { nAbs++; continue; }
    if (++perRhs[r.rhs + "|" + r.cond] > 2) continue;                // a few examples per right-hand side
    bool cnd = r.cond != "always";
    if (cnd ? nc++ < limit : nu++ < 8) keep.push_back(r);
  }
  rules = keep;
  return rules;
}
