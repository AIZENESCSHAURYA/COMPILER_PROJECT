// backend.hpp - IR lowering (three-address code), strength reduction, register VM, C emitter
#pragma once
#include "simplify.hpp"

enum VOp : uint8_t { V_CONST, V_VAR, V_ADD, V_SUB, V_MUL, V_DIV, V_NEG, V_SQRT, V_ABS, V_SIN, V_COS, V_LN, V_EXP, V_POW, V_EXPM1, V_LOG1P };
struct Ins { uint8_t op; int a, b, dst; double c; };
struct Prog { vector<Ins> code; vector<int> outs; int nregs = 0; };

struct Compiler {
  const Arena& A; bool lower; Prog P;
  unordered_map<int, int> reg; unordered_map<uint64_t, int> kreg;
  Compiler(const Arena& a, bool lw) : A(a), lower(lw) {}
  map<tuple<int, int, int>, int> vn;   // value numbering: identical pure operations are emitted once
  int emit(VOp op, int a, int b, double c = 0) {
    bool pure = op != V_CONST && op != V_VAR;
    if (pure && (op == V_ADD || op == V_MUL) && a > b) swap(a, b);
    if (pure) { auto it = vn.find({(int)op, a, b}); if (it != vn.end()) return it->second; }
    P.code.push_back({(uint8_t)op, a, b, P.nregs, c});
    if (pure) vn[{(int)op, a, b}] = P.nregs;
    return P.nregs++;
  }
  int konst(double v) {
    uint64_t bits; memcpy(&bits, &v, 8);
    auto it = kreg.find(bits); if (it != kreg.end()) return it->second;
    return kreg[bits] = emit(V_CONST, 0, 0, v);
  }
  // strength reduction: x^n -> square-and-multiply, x^-1 -> 1/x, x^0.5 -> sqrt
  int lowerPow(int r, double c, bool strength) {
    if (strength && isInt(c) && fabs(c) <= 32) {
      long m = (long)fabs(c); int res = -1, base = r;
      while (m) {
        if (m & 1) res = res < 0 ? base : emit(V_MUL, res, base);
        m >>= 1; if (m) base = emit(V_MUL, base, base);
      }
      return c < 0 ? emit(V_DIV, konst(1), res) : res;
    }
    if (c == 0.5) return emit(V_SQRT, r, 0);
    if (c == -0.5) return emit(V_DIV, konst(1), emit(V_SQRT, r, 0));
    return emit(V_POW, r, konst(c));
  }
  int gen(int n) {
    auto it = reg.find(n); if (it != reg.end()) return it->second;
    Node nd = A.n[n]; int r = 0;
    auto bin = [&](VOp o) { int x = gen(nd.a); int y = gen(nd.b); return emit(o, x, y); };
    auto un = [&](VOp o) { int x = gen(nd.a); return emit(o, x, 0); };
    switch (nd.op) {
      case NUM: r = konst(nd.val); break;
      case VAR: r = emit(V_VAR, nd.var, 0); break;
      case ADD: r = bin(V_ADD); break;
      case SUB: r = bin(V_SUB); break;
      case MUL:
        if (lower) {   // numerator / denominator form: one real division instead of multiplying by a reciprocal
          Poly p; dec(A, n, p); int num = -1, den = -1;
          auto times = [&](int acc, int v) { return acc < 0 ? v : emit(V_MUL, acc, v); };
          if (p.coef != 1 || p.f.empty()) num = konst(p.coef);
          for (auto& f : p.f) {
            int b = gen(f.first);
            if (f.second > 0) num = times(num, f.second == 1 ? b : lowerPow(b, f.second, true));
            else den = times(den, f.second == -1 ? b : lowerPow(b, -f.second, true));
          }
          r = den < 0 ? num : emit(V_DIV, num < 0 ? konst(1) : num, den);
        } else r = bin(V_MUL);
        break;
      case DIV: r = bin(V_DIV); break;
      case POW:
        if (A.n[nd.b].op == NUM && (A.n[nd.b].val == 0.5 || A.n[nd.b].val == -0.5 || lower)) { int x = gen(nd.a); r = lowerPow(x, A.n[nd.b].val, lower); }
        else r = bin(V_POW);
        break;
      case NEG: r = un(V_NEG); break;
      case SQRT: r = un(V_SQRT); break;
      case ABS: r = un(V_ABS); break;
      case SIN: r = un(V_SIN); break;
      case COS: r = un(V_COS); break;
      case LN: r = un(V_LN); break;
      case EXP: r = un(V_EXP); break;
      case EXPM1: r = un(V_EXPM1); break;
      case LOG1P: r = un(V_LOG1P); break;
    }
    return reg[n] = r;
  }
};
inline Prog compileRoots(const Arena& A, const vector<int>& roots, bool lower) {
  Compiler c(A, lower);
  for (int r : roots) { int x = c.gen(r); c.P.outs.push_back(x); }
  return c.P;
}

inline void runProg(const Prog& P, const double* x, double* r) {
  for (const Ins& i : P.code) {
    switch (i.op) {
      case V_CONST: r[i.dst] = i.c; break;
      case V_VAR: r[i.dst] = x[i.a]; break;
      case V_ADD: r[i.dst] = r[i.a] + r[i.b]; break;
      case V_SUB: r[i.dst] = r[i.a] - r[i.b]; break;
      case V_MUL: r[i.dst] = r[i.a] * r[i.b]; break;
      case V_DIV: r[i.dst] = r[i.a] / r[i.b]; break;
      case V_NEG: r[i.dst] = -r[i.a]; break;
      case V_SQRT: r[i.dst] = sqrt(r[i.a]); break;
      case V_ABS: r[i.dst] = fabs(r[i.a]); break;
      case V_SIN: r[i.dst] = sin(r[i.a]); break;
      case V_COS: r[i.dst] = cos(r[i.a]); break;
      case V_LN: r[i.dst] = log(r[i.a]); break;
      case V_EXP: r[i.dst] = exp(r[i.a]); break;
      case V_POW: r[i.dst] = pow(r[i.a], r[i.b]); break;
      case V_EXPM1: r[i.dst] = expm1(r[i.a]); break;
      case V_LOG1P: r[i.dst] = log1p(r[i.a]); break;
    }
  }
}

// One compiled output: guarded fast path + original fallback
struct Compiled {
  string name; int raw = -1, simp = -1;
  vector<Guard> guards;
  Prog fast, orig;       // fast.outs = {result, guard values...}; orig.outs = {result}
};
inline Compiled compileOutput(const Arena& A, const string& name, int raw, int simp, const vector<Guard>& gs) {
  Compiled c; c.name = name; c.raw = raw; c.simp = simp; c.guards = gs;
  vector<int> roots{simp}; for (auto& g : gs) roots.push_back(g.node);
  c.fast = compileRoots(A, roots, true);
  c.orig = compileRoots(A, {raw}, false);
  return c;
}
// returns value; sets usedFallback when a runtime guard failed
inline double evalCompiled(const Compiled& c, const double* x, double* regs, bool* usedFallback = nullptr) {
  runProg(c.fast, x, regs);
  for (size_t i = 0; i < c.guards.size(); i++) {
    if (!guardHolds(c.guards[i].k, regs[c.fast.outs[i + 1]])) {
      runProg(c.orig, x, regs);
      if (usedFallback) *usedFallback = true;
      return regs[c.orig.outs[0]];
    }
  }
  return regs[c.fast.outs[0]];
}

inline string tacStr(const Ins& i, const vector<string>& vn) {
  auto t = [](int r) { return "t" + to_string(r); };
  string d = t(i.dst) + " = ";
  switch (i.op) {
    case V_CONST: return d + fmtNum(i.c);
    case V_VAR: return d + vn[i.a];
    case V_ADD: return d + t(i.a) + " + " + t(i.b);
    case V_SUB: return d + t(i.a) + " - " + t(i.b);
    case V_MUL: return d + t(i.a) + " * " + t(i.b);
    case V_DIV: return d + t(i.a) + " / " + t(i.b);
    case V_NEG: return d + "-" + t(i.a);
    case V_SQRT: return d + "sqrt " + t(i.a);
    case V_ABS: return d + "abs " + t(i.a);
    case V_SIN: return d + "sin " + t(i.a);
    case V_COS: return d + "cos " + t(i.a);
    case V_LN: return d + "ln " + t(i.a);
    case V_EXP: return d + "exp " + t(i.a);
    case V_POW: return d + t(i.a) + " ^ " + t(i.b);
    case V_EXPM1: return d + "expm1 " + t(i.a);
    case V_LOG1P: return d + "log1p " + t(i.a);
  }
  return d;
}

// ---- C emitter ----------------------------------------------------------------------
inline string cLit(double v) {
  if (isnan(v)) return "NAN";
  if (isinf(v)) return v > 0 ? "INFINITY" : "-INFINITY";
  char b[64]; snprintf(b, sizeof b, "%.17g", v); string s = b;
  if (s.find_first_of(".eEn") == string::npos) s += ".0";
  return s;
}
inline string cBody(const Prog& P, const string& pre) {
  string o; auto t = [&](int r) { return pre + to_string(r); };
  for (auto& i : P.code) {
    string rhs;
    switch (i.op) {
      case V_CONST: rhs = cLit(i.c); break;
      case V_VAR: rhs = "x[" + to_string(i.a) + "]"; break;
      case V_ADD: rhs = t(i.a) + " + " + t(i.b); break;
      case V_SUB: rhs = t(i.a) + " - " + t(i.b); break;
      case V_MUL: rhs = t(i.a) + " * " + t(i.b); break;
      case V_DIV: rhs = t(i.a) + " / " + t(i.b); break;
      case V_NEG: rhs = "-" + t(i.a); break;
      case V_SQRT: rhs = "sqrt(" + t(i.a) + ")"; break;
      case V_ABS: rhs = "fabs(" + t(i.a) + ")"; break;
      case V_SIN: rhs = "sin(" + t(i.a) + ")"; break;
      case V_COS: rhs = "cos(" + t(i.a) + ")"; break;
      case V_LN: rhs = "log(" + t(i.a) + ")"; break;
      case V_EXP: rhs = "exp(" + t(i.a) + ")"; break;
      case V_POW: rhs = "pow(" + t(i.a) + ", " + t(i.b) + ")"; break;
      case V_EXPM1: rhs = "expm1(" + t(i.a) + ")"; break;
      case V_LOG1P: rhs = "log1p(" + t(i.a) + ")"; break;
    }
    o += "  const double " + t(i.dst) + " = " + rhs + ";\n";
  }
  return o;
}
inline string emitC(const Compiled& c, const vector<string>& vn) {
  string s = "/* " + c.name + "  inputs:";
  for (size_t i = 0; i < vn.size(); i++) s += " " + vn[i] + "=x[" + to_string(i) + "]";
  s += " */\ndouble " + c.name + "(const double *x) {\n" + cBody(c.fast, "f");
  if (c.guards.empty()) { s += "  return f" + to_string(c.fast.outs[0]) + ";\n}\n"; return s; }
  string cond;
  for (size_t i = 0; i < c.guards.size(); i++) {
    string v = "f" + to_string(c.fast.outs[i + 1]), e;
    switch (c.guards[i].k) {
      case G_NZ: e = "isfinite(" + v + ") && " + v + " != 0.0"; break;
      case G_POS: e = v + " > 0.0"; break;
      case G_NONNEG: e = v + " >= 0.0"; break;
      default: e = "isfinite(" + v + ")";
    }
    cond += (i ? " && " : "") + e;
  }
  s += "  if (" + cond + ") return f" + to_string(c.fast.outs[0]) + ";\n";
  s += "  /* a guard failed: evaluate the original expression */\n" + cBody(c.orig, "o");
  s += "  return o" + to_string(c.orig.outs[0]) + ";\n}\n";
  return s;
}
