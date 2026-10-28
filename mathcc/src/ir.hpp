// ir.hpp - hash-consed expression DAG, interval/definedness analysis, printer, reference evaluator
#pragma once
#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;

enum Op : uint8_t { NUM, VAR, ADD, SUB, MUL, DIV, POW, NEG, SQRT, ABS, SIN, COS, LN, EXP, EXPM1, LOG1P };
static const double INF = numeric_limits<double>::infinity();

// ---------------------------------------------------------------------------
// Abstract domain: interval + "zero excluded" + "definitely a finite real".
// Contract: if def==true the node is a finite real number for every input that
// satisfies the assumptions (overflow is ignored). The interval bounds that value.
// ---------------------------------------------------------------------------
struct Iv { double lo = -INF, hi = INF; bool nz = false, def = false; };

inline bool isInt(double c) { return fabs(c) < 1e9 && c == floor(c); }
inline bool ivPos(const Iv& v) { return v.lo > 0 || (v.lo >= 0 && v.nz); }
inline bool ivNeg(const Iv& v) { return v.hi < 0 || (v.hi <= 0 && v.nz); }
inline bool ivNZ(const Iv& v) { return v.lo > 0 || v.hi < 0 || v.nz; }
inline double smul(double a, double b) { return (a == 0 || b == 0) ? 0 : a * b; }

inline Iv ivNegate(const Iv& a) { Iv r; r.lo = -a.hi; r.hi = -a.lo; r.nz = a.nz; r.def = a.def; return r; }
inline Iv ivAdd(const Iv& a, const Iv& b) {
  Iv r; r.lo = a.lo + b.lo; r.hi = a.hi + b.hi; r.def = a.def && b.def;
  bool nn = a.lo >= 0 && b.lo >= 0, np = a.hi <= 0 && b.hi <= 0;
  r.nz = (nn && (ivPos(a) || ivPos(b))) || (np && (ivNeg(a) || ivNeg(b)));
  return r;
}
inline Iv ivMul(const Iv& a, const Iv& b) {
  double c[4] = {smul(a.lo, b.lo), smul(a.lo, b.hi), smul(a.hi, b.lo), smul(a.hi, b.hi)};
  Iv r; r.lo = *min_element(c, c + 4); r.hi = *max_element(c, c + 4);
  r.nz = ivNZ(a) && ivNZ(b); r.def = a.def && b.def; return r;
}
inline Iv ivPowInt(const Iv& a, int n) {
  Iv r; r.def = a.def;
  if (n == 0) { r.lo = r.hi = 1; r.nz = true; r.def = true; return r; }
  if (n > 0) {
    r.nz = ivNZ(a);
    if (n % 2 == 0) {
      double l = fabs(a.lo), h = fabs(a.hi), mx = max(l, h);
      double mn = (a.lo <= 0 && a.hi >= 0) ? 0 : min(l, h);
      r.lo = pow(mn, n); r.hi = pow(mx, n);
    } else { r.lo = pow(a.lo, n); r.hi = pow(a.hi, n); }
    return r;
  }
  if (!ivNZ(a)) { r.def = false; return r; }   // 1/0 possible -> not defined
  Iv p = ivPowInt(a, -n);
  r.nz = true;
  if (ivPos(p)) { r.lo = isinf(p.hi) ? 0 : 1.0 / p.hi; r.hi = p.lo <= 0 ? INF : 1.0 / p.lo; }
  else if (ivNeg(p)) { r.lo = p.hi >= 0 ? -INF : 1.0 / p.hi; r.hi = isinf(p.lo) ? 0 : 1.0 / p.lo; }
  return r;
}
inline Iv ivPowReal(const Iv& a, double c) {   // c non-integer
  Iv r;
  if (c > 0) {
    if (a.lo >= 0) { r.lo = pow(a.lo, c); r.hi = pow(a.hi, c); r.nz = ivNZ(a); r.def = a.def; }
    else { r.lo = 0; r.hi = INF; r.def = false; }
  } else {
    if (ivPos(a)) { r.lo = isinf(a.hi) ? 0 : pow(a.hi, c); r.hi = a.lo <= 0 ? INF : pow(a.lo, c); r.nz = true; r.def = a.def; }
    else { r.lo = 0; r.hi = INF; r.def = false; }
  }
  return r;
}

// ---------------------------------------------------------------------------
struct Node { Op op = NUM; int a = -1, b = -1; double val = 0; int var = -1; Iv iv; };

struct Arena {
  vector<Node> n;
  vector<string> varNames;
  vector<Iv> varIv;
  unordered_map<string, int> memo;

  Iv calc(const Node& nd) const {
    auto I = [&](int i) -> const Iv& { return n[i].iv; };
    switch (nd.op) {
      case NUM: { Iv r; if (isfinite(nd.val)) { r.lo = r.hi = nd.val; r.nz = nd.val != 0; r.def = true; } return r; }
      case VAR: { Iv r = varIv[nd.var]; r.def = true; return r; }
      case ADD: return ivAdd(I(nd.a), I(nd.b));
      case SUB: return ivAdd(I(nd.a), ivNegate(I(nd.b)));
      case MUL: return ivMul(I(nd.a), I(nd.b));
      case DIV: return ivMul(I(nd.a), ivPowInt(I(nd.b), -1));
      case POW: {
        const Node& e = n[nd.b];
        if (e.op == NUM && isfinite(e.val)) return isInt(e.val) ? ivPowInt(I(nd.a), (int)e.val) : ivPowReal(I(nd.a), e.val);
        return Iv();
      }
      case NEG: return ivNegate(I(nd.a));
      case SQRT: return ivPowReal(I(nd.a), 0.5);
      case ABS: {
        const Iv& a = I(nd.a); Iv r; r.def = a.def; r.nz = ivNZ(a);
        if (a.lo >= 0) { r.lo = a.lo; r.hi = a.hi; }
        else if (a.hi <= 0) { r.lo = -a.hi; r.hi = -a.lo; }
        else { r.lo = 0; r.hi = max(-a.lo, a.hi); }
        return r;
      }
      case SIN: case COS: { Iv r; r.lo = -1; r.hi = 1; r.def = I(nd.a).def; return r; }
      case LN: {
        const Iv& a = I(nd.a); Iv r;
        if (ivPos(a) && a.def) { r.lo = log(a.lo); r.hi = log(a.hi); r.def = true; }
        return r;
      }
      case EXP: { const Iv& a = I(nd.a); Iv r; r.lo = exp(a.lo); r.hi = exp(a.hi); r.nz = a.lo > -700; r.def = a.def && a.hi < 700; return r; }   // exp overflows above ~709
      case EXPM1: { const Iv& a = I(nd.a); Iv r; r.lo = expm1(a.lo); r.hi = expm1(a.hi); r.nz = ivNZ(a); r.def = a.def; return r; }
      case LOG1P: {
        const Iv& a = I(nd.a); Iv r;
        if (a.lo > -1 && a.def) { r.lo = log1p(a.lo); r.hi = log1p(a.hi); r.nz = ivNZ(a); r.def = true; }
        return r;
      }
    }
    return Iv();
  }

  int intern(const Node& nd) {
    int64_t key[4]; uint64_t bits; memcpy(&bits, &nd.val, 8);
    key[0] = nd.op; key[1] = nd.a; key[2] = (nd.op == VAR ? nd.var : nd.b); key[3] = (int64_t)bits;
    string s((const char*)key, sizeof key);
    auto it = memo.find(s);
    if (it != memo.end()) return it->second;
    n.push_back(nd);
    int id = (int)n.size() - 1; memo[s] = id; return id;
  }
  int num(double v) {
    if (v == 0) v = 0.0;                       // +0 and -0 are identified (documented contract)
    if (isnan(v)) v = numeric_limits<double>::quiet_NaN();
    Node nd; nd.op = NUM; nd.val = v; nd.iv = calc(nd); return intern(nd);
  }
  int mk(Op op, int a, int b = -1) {
    Node nd; nd.op = op; nd.a = a; nd.b = b; nd.iv = calc(nd); return intern(nd);
  }
  int newVar(const string& name) { varNames.push_back(name); Iv v; v.def = true; varIv.push_back(v); return (int)varNames.size() - 1; }
  int var(int idx) { Node nd; nd.op = VAR; nd.var = idx; nd.iv = calc(nd); return intern(nd); }
  bool isNum(int id) const { return n[id].op == NUM; }
};

// Product decomposition: node == coef * prod(base_i ^ exp_i)
struct Poly { double coef = 1; vector<pair<int, double>> f; };
inline void dec(const Arena& A, int id, Poly& p) {
  const Node& nd = A.n[id];
  if (nd.op == NUM) { p.coef *= nd.val; return; }
  if (nd.op == MUL) { dec(A, nd.a, p); dec(A, nd.b, p); return; }
  if (nd.op == POW && A.n[nd.b].op == NUM) { p.f.push_back({nd.a, A.n[nd.b].val}); return; }
  p.f.push_back({id, 1.0});
}

// ---------------------------------------------------------------------------
inline string fmtNum(double v) {
  if (isnan(v)) return "nan";
  if (isinf(v)) return v > 0 ? "inf" : "-inf";
  char buf[64]; snprintf(buf, sizeof buf, "%.12g", v); return buf;
}

inline string showR(const Arena& A, int id, int pp) {
  Node nd = A.n[id]; string s; int prec = 5;
  auto par = [&](const string& x) { return "(" + x + ")"; };
  switch (nd.op) {
    case NUM: s = fmtNum(nd.val); if (nd.val < 0) prec = 3; break;
    case VAR: s = A.varNames[nd.var]; break;
    case ADD: {
      string l = showR(A, nd.a, 1), r = showR(A, nd.b, 2);
      s = (!r.empty() && r[0] == '-') ? l + " - " + r.substr(1) : l + " + " + r; prec = 1; break;
    }
    case SUB: {
      string l = showR(A, nd.a, 1), r = showR(A, nd.b, 2);
      if (!r.empty() && r[0] == '-') r = par(r);
      s = l + " - " + r; prec = 1; break;
    }
    case MUL: {
      Poly p; dec(A, id, p);
      vector<string> num, den;
      auto fac = [&](int b, double e) {
        double ae = fabs(e);
        if (ae == 0.5) return "sqrt(" + showR(A, b, 0) + ")";
        string bs = showR(A, b, 5);
        return ae == 1 ? bs : bs + "^" + fmtNum(ae);
      };
      for (auto& [b, e] : p.f) (e > 0 ? num : den).push_back(fac(b, e));
      string sign = p.coef < 0 ? "-" : "";
      double ac = fabs(p.coef);
      if (ac != 1) num.insert(num.begin(), fmtNum(ac));
      string ns; for (size_t i = 0; i < num.size(); i++) ns += (i ? "*" : "") + num[i];
      if (ns.empty()) ns = "1";
      if (den.empty()) s = sign + ns;
      else {
        string ds; for (size_t i = 0; i < den.size(); i++) ds += (i ? "*" : "") + den[i];
        if (den.size() > 1) ds = par(ds);
        s = sign + ns + "/" + ds;
      }
      prec = 2; break;
    }
    case NEG: s = "-" + showR(A, nd.a, 3); prec = 3; break;
    case DIV: s = showR(A, nd.a, 2) + "/" + showR(A, nd.b, 3); prec = 2; break;
    case POW: {
      if (A.n[nd.b].op == NUM) {
        double c = A.n[nd.b].val;
        if (c == 0.5) { s = "sqrt(" + showR(A, nd.a, 0) + ")"; break; }
        string e = fmtNum(c); if (c < 0) e = par(e);
        s = showR(A, nd.a, 5) + "^" + e;
      } else s = showR(A, nd.a, 5) + "^" + showR(A, nd.b, 5);
      prec = 4; break;
    }
    case SQRT: s = "sqrt(" + showR(A, nd.a, 0) + ")"; break;
    case ABS: s = "abs(" + showR(A, nd.a, 0) + ")"; break;
    case SIN: s = "sin(" + showR(A, nd.a, 0) + ")"; break;
    case COS: s = "cos(" + showR(A, nd.a, 0) + ")"; break;
    case LN: s = "ln(" + showR(A, nd.a, 0) + ")"; break;
    case EXP: s = "exp(" + showR(A, nd.a, 0) + ")"; break;
    case EXPM1: s = "expm1(" + showR(A, nd.a, 0) + ")"; break;
    case LOG1P: s = "log1p(" + showR(A, nd.a, 0) + ")"; break;
  }
  return prec < pp ? par(s) : s;
}
inline string show(const Arena& A, int id) { return showR(A, id, 0); }

// Reference (naive) evaluator: walks the DAG as a tree, no sharing, no tricks.
template <class T>
inline T evalTreeT(const Arena& A, int id, const double* x) {
  const Node& nd = A.n[id];
  auto E = [&](int c) { return evalTreeT<T>(A, c, x); };
  switch (nd.op) {
    case NUM: return (T)nd.val;
    case VAR: return (T)x[nd.var];
    case ADD: return E(nd.a) + E(nd.b);
    case SUB: return E(nd.a) - E(nd.b);
    case MUL: return E(nd.a) * E(nd.b);
    case DIV: return E(nd.a) / E(nd.b);
    case POW:   // language semantics: x^0.5 is sqrt(x), x^-0.5 is 1/sqrt(x) (pow() differs at -inf)
      if (A.n[nd.b].op == NUM && A.n[nd.b].val == 0.5) return std::sqrt(E(nd.a));
      if (A.n[nd.b].op == NUM && A.n[nd.b].val == -0.5) return (T)1 / std::sqrt(E(nd.a));
      return std::pow(E(nd.a), E(nd.b));
    case NEG: return -E(nd.a);
    case SQRT: return std::sqrt(E(nd.a));
    case ABS: return std::fabs(E(nd.a));
    case SIN: return std::sin(E(nd.a));
    case COS: return std::cos(E(nd.a));
    case LN: return std::log(E(nd.a));
    case EXP: return std::exp(E(nd.a));
    case EXPM1: return std::expm1(E(nd.a));
    case LOG1P: return std::log1p(E(nd.a));
  }
  return 0;
}
inline double evalTree(const Arena& A, int id, const double* x) { return evalTreeT<double>(A, id, x); }

inline int countNodes(const Arena& A, int root) {
  unordered_set<int> seen; vector<int> st{root};
  while (!st.empty()) {
    int u = st.back(); st.pop_back();
    if (!seen.insert(u).second) continue;
    if (A.n[u].a >= 0) st.push_back(A.n[u].a);
    if (A.n[u].b >= 0) st.push_back(A.n[u].b);
  }
  return (int)seen.size();
}
