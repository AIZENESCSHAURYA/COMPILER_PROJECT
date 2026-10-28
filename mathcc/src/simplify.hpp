// simplify.hpp - guarded symbolic simplifier (the novel part) + derivative
//
// Every rewrite that is NOT an identity on all IEEE doubles carries a side condition
// ("guard").  A guard is discharged in one of three ways:
//   1. statically, from the interval/definedness facts of the node (assumptions),
//   2. at run time: the guard becomes an extra output of the compiled program and
//      the generated code falls back to the original expression when it fails,
//   3. never (conservative mode / refuted by intervals): the rewrite is skipped.
// Each applied rewrite is recorded as a Step so an independent checker can certify it.
#pragma once
#include "ir.hpp"

enum GK { G_NZ, G_POS, G_NONNEG, G_DEF };
struct Guard { GK k; int node; };
enum Mode { M_GUARDED, M_CONSERVATIVE, M_UNSAFE };
struct Step { int pre, post; vector<Guard> gs; vector<char> proven; string rule; };   // pre == post wherever all gs hold

inline string guardStr(const Arena& A, const Guard& g) {
  string e = show(A, g.node);
  switch (g.k) {
    case G_NZ: return e + " != 0";
    case G_POS: return e + " > 0";
    case G_NONNEG: return e + " >= 0";
    default: return "finite(" + e + ")";
  }
}
inline bool guardHolds(GK k, double v) {
  switch (k) {
    case G_NZ: return isfinite(v) && v != 0;
    case G_POS: return v > 0;
    case G_NONNEG: return v >= 0;
    default: return isfinite(v);
  }
}

struct Simplifier {
  Arena& A; Mode mode;
  vector<Guard> guards;            // runtime guards required by the result
  set<pair<int, int>> gseen;
  vector<Step> steps;              // certificate trace
  vector<Guard> cur;               // guards used by the rewrite step in progress
  string rule;                     // name of the rewrite rule that fired in the current step
  vector<string> refused;          // rewrites that were skipped, with the reason
  void R(const char* r) { if (rule.empty()) rule = r; }
  void recordStep(int pre, int post, const string& rl) {
    Step st{pre, post, cur, {}, rl};
    for (auto& g : cur) st.proven.push_back(mode == M_UNSAFE ? 2 : (proven(g) ? 1 : 0));
    steps.push_back(st);
  }
  unordered_map<int, int> memo;
  int nProven = 0, nRuntime = 0, nRefused = 0;

  Simplifier(Arena& a, Mode m) : A(a), mode(m) {}

  // ---- guard handling -----------------------------------------------------
  bool proven(const Guard& g) {
    const Iv& v = A.n[g.node].iv;
    switch (g.k) {
      case G_DEF: return v.def;
      case G_NZ: return v.def && ivNZ(v);
      case G_POS: return v.def && ivPos(v);
      default: return v.def && v.lo >= 0;
    }
  }
  bool refuted(const Guard& g) {
    const Iv& v = A.n[g.node].iv;
    switch (g.k) {
      case G_NZ: return v.lo == 0 && v.hi == 0;
      case G_POS: return v.hi <= 0;
      case G_NONNEG: return v.hi < 0;
      default: return false;
    }
  }
  bool tryGuards(const vector<Guard>& gs) {
    if (mode == M_UNSAFE) { for (auto& g : gs) cur.push_back(g); return true; }
    bool needRt = false;
    for (auto& g : gs) {
      if (proven(g)) continue;
      if (refuted(g)) { nRefused++; refused.push_back(guardStr(A, g) + "|this condition is provably false for your assumptions"); return false; }
      needRt = true;
    }
    if (needRt && mode == M_CONSERVATIVE) {
      nRefused++;
      for (auto& g : gs) if (!proven(g)) { refused.push_back(guardStr(A, g) + "|cannot be proven from your assumptions, and conservative mode does not allow run-time checks"); break; }
      return false;
    }
    for (auto& g : gs) {
      cur.push_back(g);
      if (proven(g)) { nProven++; continue; }
      if (gseen.insert({(int)g.k, g.node}).second) { guards.push_back(g); nRuntime++; }
    }
    return true;
  }

  // ---- canonical product / sum construction --------------------------------
  int build(Poly p) {
    if (p.coef == 0) {                       // never drop factors: 0*e is NaN when e is NaN or infinite
      if (p.f.empty()) return A.num(p.coef);
      double c = p.coef; p.coef = 1; return A.mk(MUL, A.num(c), build(p));
    }
    sort(p.f.begin(), p.f.end());
    int acc = -1;
    if (p.coef != 1) acc = A.num(p.coef);
    for (auto& [b, e] : p.f) {
      int t = (e == 1) ? b : A.mk(POW, b, A.num(e));
      acc = acc < 0 ? t : A.mk(MUL, acc, t);
    }
    return acc < 0 ? A.num(1) : acc;
  }
  int mulConst(int x, double c) { Poly p; dec(A, x, p); p.coef *= c; return build(p); }

  bool canMerge(int b, double a, double e) {
    bool ia = isInt(a), ie = isInt(e); double s = a + e;
    if (ia && ie) { if ((a > 0 && e > 0) || (a < 0 && e < 0)) return true; return tryGuards({{G_NZ, b}}); }
    if (a > 0 && e > 0) return tryGuards({{G_NONNEG, b}});   // fractional exponents: x^a is NaN for x<0, and pow() differs at -inf
    return tryGuards({{G_POS, b}});
  }
  void normFactors(Poly& p) {
    for (auto& f : p.f)   // |y|^even == y^even
      if (A.n[f.first].op == ABS && isInt(f.second) && fmod(f.second, 2) == 0) f.first = A.n[f.first].a;
    vector<pair<int, double>> out;
    for (auto& [b, e] : p.f) {
      bool merged = false;
      for (auto& q : out) if (q.first == b && canMerge(b, q.second, e)) { R(q.second + e == 0 ? "cancel-factor" : "merge-exponents"); q.second += e; merged = true; break; }
      if (!merged) out.push_back({b, e});
    }
    p.f.clear();
    for (auto& q : out) if (q.second != 0) p.f.push_back(q);
  }

  int mulN(int x, int y) {
    Poly p; dec(A, x, p); dec(A, y, p);
    if (p.coef == 0) {
      R("zero-product");
      // 0*e = 0 only if e is a finite number (0*NaN and 0*inf are NaN). The sign of zero is not tracked.
      if (p.f.empty()) return A.num(0);
      Poly q = p; q.coef = 1; int rest = build(q);
      if (tryGuards({{G_DEF, rest}})) return A.num(0);
      return A.mk(MUL, x, y);
    }
    normFactors(p);
    return build(p);
  }

  struct Term { int node; double c; };
  // sc is an exact scale (+1 or -1): negation distributes over sums for free
  void gather(int n, double sc, vector<Term>& ts, double& c0) {
    Node nd = A.n[n];
    if (nd.op == ADD) { gather(nd.a, sc, ts, c0); gather(nd.b, sc, ts, c0); return; }
    if (nd.op == NUM) { c0 += sc * nd.val; return; }
    Poly p; dec(A, n, p);
    if (p.coef == 0) { ts.push_back({n, sc}); return; }
    if ((p.coef == -1 || p.coef == 1) && p.f.size() == 1 && p.f[0].second == 1 && A.n[p.f[0].first].op == ADD) {
      R("distribute-negation"); gather(p.f[0].first, sc * p.coef, ts, c0); return;
    }
    double c = p.coef; p.coef = 1;
    ts.push_back({build(p), c * sc});
  }
  int addN(int x, int y) {
    vector<Term> ts; double c0 = 0; gather(x, 1, ts, c0); gather(y, 1, ts, c0);
    vector<Term> out;
    for (auto& t : ts) {
      bool m = false;
      for (auto& q : out) if (q.node == t.node) {
        double s = q.c + t.c;
        if (s == 0 && !tryGuards({{G_DEF, t.node}})) continue;
        R(s == 0 ? "cancel-terms" : "combine-terms");
        q.c = s; m = true; break;
      }
      if (!m) out.push_back(t);
    }
    // sin(y)^2 + cos(y)^2 = 1   (needs finite(y))
    for (size_t i = 0; i < out.size(); i++) {
      if (out[i].c == 0) continue;
      Poly p; dec(A, out[i].node, p);
      if (!(p.coef == 1 && p.f.size() == 1 && p.f[0].second == 2 && A.n[p.f[0].first].op == SIN)) continue;
      int y = A.n[p.f[0].first].a;
      Poly q; q.f.push_back({A.mk(COS, y), 2.0});
      int cn = build(q);
      for (size_t j = 0; j < out.size(); j++)
        if (j != i && out[j].node == cn && out[j].c == out[i].c && tryGuards({{G_DEF, y}})) {
          R("trig-identity"); c0 += out[i].c; out[i].c = 0; out[j].c = 0; break;
        }
    }
    sort(out.begin(), out.end(), [](const Term& a, const Term& b) { return a.node < b.node; });
    int acc = -1;
    for (auto& t : out) {
      if (t.c == 0) continue;
      int tn = (t.c == 1) ? t.node : mulConst(t.node, t.c);
      acc = acc < 0 ? tn : A.mk(ADD, acc, tn);
    }
    if (c0 != 0) { int cn = A.num(c0); acc = acc < 0 ? cn : A.mk(ADD, acc, cn); }
    return acc < 0 ? A.num(0) : acc;
  }

  int absN(int x) {
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(fabs(nx.val)); }
    if (nx.op == ABS) { R("abs-idempotent"); return x; }
    Iv v = nx.iv;
    if (v.lo >= 0) { R("abs-sign"); return x; }
    if (v.hi <= 0) { R("abs-sign"); return mulConst(x, -1); }
    Poly p; dec(A, x, p);
    if (p.coef < 0) return absN(mulConst(x, -1));
    return A.mk(ABS, x);
  }
  int powN(int x, double a) {
    if (a == 1) return x;
    if (a == 0) return A.num(1);
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(pow(nx.val, a)); }
    Poly p; dec(A, x, p);
    if (p.coef == 0 || isinf(p.coef)) return A.mk(POW, x, A.num(a));   // 0 or inf coefficient: keep it opaque
    if (isInt(a)) {
      vector<Guard> need;
      for (auto& f : p.f) if (!isInt(f.second)) need.push_back({(f.second > 0 && a > 0) ? G_NONNEG : G_POS, f.first});
      if (!need.empty() && !tryGuards(need)) return A.mk(POW, x, A.num(a));
      if (nx.op == MUL || nx.op == POW) R("power-of-power");
      p.coef = pow(p.coef, a);
      for (auto& f : p.f) f.second *= a;
      normFactors(p);
      return build(p);
    }
    if (p.coef == 1 && p.f.size() == 1) {
      auto [b, e] = p.f[0];
      if (e != 1) {
        if (isInt(e) && fmod(e, 2) == 0) { R("abs-from-sqrt"); return powN(absN(b), e * a); }   // (y^2k)^a = |y|^(2ka)
        if (tryGuards({{(e > 0 && a > 0) ? G_NONNEG : G_POS, b}})) { R("power-of-power"); return powN(b, e * a); }
      }
    }
    return A.mk(POW, x, A.num(a));
  }
  int sinN(int x) {
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(sin(nx.val)); }
    Poly p; dec(A, x, p);
    if (p.coef < 0) { R("odd-even"); return mulConst(sinN(mulConst(x, -1)), -1); }
    return A.mk(SIN, x);
  }
  int cosN(int x) {
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(cos(nx.val)); }
    Poly p; dec(A, x, p);
    if (p.coef < 0) { R("odd-even"); return cosN(mulConst(x, -1)); }
    return A.mk(COS, x);
  }
  int lnN(int x) {
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(log(nx.val)); }
    if (nx.op == EXP && tryGuards({{G_NZ, x}})) { R("ln-exp"); return nx.a; }         // ln(exp y) = y  (exp must neither overflow nor underflow)
    if (nx.op == POW && A.n[nx.b].op == NUM) {                       // ln(y^c) = c ln y
      double c = A.n[nx.b].val; int y = nx.a;
      if (isInt(c) && fmod(c, 2) == 0) { R("ln-power"); return mulN(A.num(c), lnN(absN(y))); }
      if (tryGuards({{G_POS, y}})) { R("ln-power"); return mulN(A.num(c), lnN(y)); }
    }
    return A.mk(LN, x);
  }
  int expN(int x) {
    Node nx = A.n[x];
    if (nx.op == NUM) { R("fold-constants"); return A.num(exp(nx.val)); }
    if (nx.op == LN && tryGuards({{G_NONNEG, nx.a}})) { R("exp-ln"); return nx.a; }   // exp(ln y) = y
    return A.mk(EXP, x);
  }

  // ---- stability-aware rewrites (applied to the raw DAG before simplification) ----
  unordered_map<int, int> smemo;
  int stab(int n) {
    auto it = smemo.find(n); if (it != smemo.end()) return it->second;
    Node nd = A.n[n]; int r = n;
    if (nd.op != NUM && nd.op != VAR) {
      int a = stab(nd.a), b = nd.b >= 0 ? stab(nd.b) : -1;
      r = (a == nd.a && b == nd.b) ? n : A.mk(nd.op, a, b);
      Node na = A.n[a]; Node nb = b >= 0 ? A.n[b] : Node();
      cur.clear(); int pre = r, post = -1; string srule;
      auto one = [&](const Node& x) { return x.op == NUM && x.val == 1; };
      if (nd.op == SUB && one(na) && nb.op == COS)                       // 1 - cos y = 2 sin^2(y/2)
        { srule = "stable-1-cos"; post = A.mk(MUL, A.num(2), A.mk(POW, A.mk(SIN, A.mk(DIV, nb.a, A.num(2))), A.num(2))); }
      else if (nd.op == SUB && na.op == COS && one(nb))                  // cos y - 1 = -2 sin^2(y/2)
        { srule = "stable-1-cos"; post = A.mk(MUL, A.num(-2), A.mk(POW, A.mk(SIN, A.mk(DIV, na.a, A.num(2))), A.num(2))); }
      else if (nd.op == SUB && na.op == EXP && one(nb)) { srule = "stable-expm1"; post = A.mk(EXPM1, na.a); }       // exp y - 1 = expm1 y
      else if (nd.op == SUB && na.op == SQRT && nb.op == SQRT) {         // sqrt u - sqrt v = (u-v)/(sqrt u + sqrt v)
        int den = A.mk(ADD, a, b);
        if (tryGuards({{G_NZ, den}})) { srule = "stable-sqrt-diff"; post = A.mk(DIV, A.mk(SUB, na.a, nb.a), den); }
      }
      else if (nd.op == LN && na.op == ADD && one(A.n[na.a])) { srule = "stable-log1p"; post = A.mk(LOG1P, na.b); }  // ln(1+y) = log1p y
      else if (nd.op == LN && na.op == ADD && one(A.n[na.b])) { srule = "stable-log1p"; post = A.mk(LOG1P, na.a); }
      if (post >= 0) { recordStep(pre, post, srule); r = post; }
    }
    return smemo[n] = r;
  }

  // ---- driver -----------------------------------------------------------------
  int S(int n) {
    auto it = memo.find(n);
    if (it != memo.end()) return it->second;
    Node nd = A.n[n]; int r, pre = n;
    if (nd.op == NUM || nd.op == VAR) { memo[n] = n; return n; }
    int sa = S(nd.a), sb = nd.b >= 0 ? S(nd.b) : -1;
    pre = A.mk(nd.op, sa, sb);
    cur.clear(); rule.clear();
    switch (nd.op) {
      case ADD: r = addN(sa, sb); break;
      case SUB: r = addN(sa, mulConst(sb, -1)); break;
      case NEG: r = mulConst(sa, -1); break;
      case MUL: r = mulN(sa, sb); break;
      case DIV: r = mulN(sa, powN(sb, -1)); break;
      case POW: r = A.isNum(sb) ? powN(sa, A.n[sb].val) : A.mk(POW, sa, sb); break;
      case SQRT: r = powN(sa, 0.5); break;
      case ABS: r = absN(sa); break;
      case SIN: r = sinN(sa); break;
      case COS: r = cosN(sa); break;
      case LN: r = lnN(sa); break;
      case EXP: r = expN(sa); break;
      case EXPM1: case LOG1P: r = A.mk(nd.op, sa); break;
      default: r = n;
    }
    if (pre != r) {
      if (rule.empty()) switch (nd.op) {
        case DIV: rule = "division-as-power"; break;
        case SUB: rule = "subtraction-as-term"; break;
        case SQRT: rule = "sqrt-as-power"; break;
        case NEG: rule = "negation-as-coefficient"; break;
        case ADD: case MUL: rule = (A.isNum(sa) && A.isNum(sb)) ? "fold-constants" : "canonical-form"; break;
        default: rule = "canonical-form";
      }
      recordStep(pre, r, rule);
    }
    memo[n] = r;
    return r;
  }
};

// ---------------------------------------------------------------------------
// Symbolic differentiation on the raw DAG (structurally-zero terms are pruned,
// so the derivative itself has no 0*x junk that would need guards).
// ---------------------------------------------------------------------------
struct Differ {
  Arena& A; int v;
  unordered_map<int, bool> depM; unordered_map<int, int> memo;
  Differ(Arena& a, int var) : A(a), v(var) {}
  bool dep(int n) {
    auto it = depM.find(n); if (it != depM.end()) return it->second;
    Node nd = A.n[n]; bool r;
    if (nd.op == NUM) r = false;
    else if (nd.op == VAR) r = nd.var == v;
    else r = dep(nd.a) || (nd.b >= 0 && dep(nd.b));
    return depM[n] = r;
  }
  bool Z(int x) { return A.isNum(x) && A.n[x].val == 0; }
  bool O(int x) { return A.isNum(x) && A.n[x].val == 1; }
  int radd(int a, int b) { if (Z(a)) return b; if (Z(b)) return a; return A.mk(ADD, a, b); }
  int rsub(int a, int b) { if (Z(b)) return a; if (Z(a)) return A.mk(NEG, b); return A.mk(SUB, a, b); }
  int rneg(int a) { return Z(a) ? a : A.mk(NEG, a); }
  int rmul(int a, int b) { if (Z(a) || Z(b)) return A.num(0); if (O(a)) return b; if (O(b)) return a; return A.mk(MUL, a, b); }
  int rdiv(int a, int b) { if (Z(a)) return a; if (O(b)) return a; return A.mk(DIV, a, b); }
  int rpow(int a, double e) { if (e == 1) return a; if (e == 0) return A.num(1); return A.mk(POW, a, A.num(e)); }
  int D(int n) {
    if (!dep(n)) return A.num(0);
    auto it = memo.find(n); if (it != memo.end()) return it->second;
    Node nd = A.n[n]; int a = nd.a, b = nd.b, r = 0;
    switch (nd.op) {
      case VAR: r = A.num(1); break;
      case ADD: r = radd(D(a), D(b)); break;
      case SUB: r = rsub(D(a), D(b)); break;
      case NEG: r = rneg(D(a)); break;
      case MUL: r = radd(rmul(D(a), b), rmul(a, D(b))); break;
      case DIV:
        if (!dep(b)) r = rdiv(D(a), b);
        else r = rdiv(rsub(rmul(D(a), b), rmul(a, D(b))), rpow(b, 2));
        break;
      case POW:
        if (A.isNum(b)) { double c = A.n[b].val; r = rmul(rmul(A.num(c), rpow(a, c - 1)), D(a)); }
        else if (!dep(b)) r = rmul(rmul(b, A.mk(POW, a, A.mk(SUB, b, A.num(1)))), D(a));
        else if (!dep(a)) r = rmul(rmul(n, A.mk(LN, a)), D(b));
        else r = rmul(n, radd(rmul(D(b), A.mk(LN, a)), rdiv(rmul(b, D(a)), a)));
        break;
      case SQRT: r = rdiv(D(a), rmul(A.num(2), n)); break;
      case ABS: r = rmul(D(a), rdiv(a, n)); break;
      case SIN: r = rmul(A.mk(COS, a), D(a)); break;
      case COS: r = rneg(rmul(A.mk(SIN, a), D(a))); break;
      case LN: r = rdiv(D(a), a); break;
      case EXP: r = rmul(n, D(a)); break;
      default: r = A.num(0);
    }
    return memo[n] = r;
  }
};
