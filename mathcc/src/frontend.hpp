// frontend.hpp - lexer, recursive-descent parser, symbol table / semantic checks
//
// Language (one statement per line, '#' starts a comment):
//   assume x > 0            assume x >= 0     assume x != 0     assume x in [1, 10]
//   name = expression       (defines an output and a reusable name)
//   expression              (anonymous output)
// expression: + - * / ^ ( ), sin cos ln log exp sqrt abs, d(expr, var), constants pi and e
#pragma once
#include "simplify.hpp"

struct CompileError : runtime_error { using runtime_error::runtime_error; };
// Errors: thrown normally; in builds without C++ exceptions (WebAssembly) they print and exit(1).
[[noreturn]] inline void raiseError(const string& m) {
#ifdef MATHCC_NO_EXCEPTIONS
  fprintf(stderr, "error: %s\n", m.c_str()); exit(1);
#else
  throw CompileError(m);
#endif
}

struct Tok { enum K { NUM, ID, SYM, END } k; string s; double v = 0; int col = 0; };

inline vector<Tok> lexLine(const string& line, int ln) {
  vector<Tok> t; size_t i = 0;
  auto err = [&](const string& m) { raiseError("line " + to_string(ln) + ", col " + to_string(i + 1) + ": " + m); };
  while (i < line.size()) {
    char c = line[i];
    if (c == '#') break;
    if (isspace((unsigned char)c)) { i++; continue; }
    Tok k; k.col = (int)i;
    if (isdigit((unsigned char)c) || (c == '.' && i + 1 < line.size() && isdigit((unsigned char)line[i + 1]))) {
      size_t j = i; while (j < line.size() && (isdigit((unsigned char)line[j]) || line[j] == '.')) j++;
      if (j < line.size() && (line[j] == 'e' || line[j] == 'E')) {
        size_t m = j + 1; if (m < line.size() && (line[m] == '+' || line[m] == '-')) m++;
        if (m < line.size() && isdigit((unsigned char)line[m])) { while (m < line.size() && isdigit((unsigned char)line[m])) m++; j = m; }
      }
      k.k = Tok::NUM; k.s = line.substr(i, j - i); k.v = strtod(k.s.c_str(), nullptr); i = j;
    } else if (isalpha((unsigned char)c) || c == '_') {
      size_t j = i; while (j < line.size() && (isalnum((unsigned char)line[j]) || line[j] == '_')) j++;
      k.k = Tok::ID; k.s = line.substr(i, j - i); i = j;
    } else {
      string two = line.substr(i, 2);
      if (two == ">=" || two == "<=" || two == "!=") { k.k = Tok::SYM; k.s = two; i += 2; }
      else if (string("+-*/^(),=<>[]").find(c) != string::npos) { k.k = Tok::SYM; k.s = string(1, c); i++; }
      else err(string("unexpected character '") + c + "'");
    }
    t.push_back(k);
  }
  Tok e; e.k = Tok::END; e.col = (int)line.size(); t.push_back(e);
  return t;
}

struct Output { string name; int raw; };

struct Parser {
  Arena& A;
  map<string, int> names;      // defined names -> node
  map<string, int> vars;       // input variables -> index
  vector<Output> outs;
  vector<Tok> t; size_t p = 0; int ln = 0; int anon = 0;
  bool dumpTokens = false;

  Parser(Arena& a) : A(a) {}
  [[noreturn]] void fail(const string& m) { raiseError("line " + to_string(ln) + ", col " + to_string(t[min(p, t.size() - 1)].col + 1) + ": " + m); }
  bool isSym(const char* s) { return t[p].k == Tok::SYM && t[p].s == s; }
  void expect(const char* s) { if (!isSym(s)) fail(string("expected '") + s + "'"); p++; }

  int varIndex(const string& name) {
    if (names.count(name)) fail("'" + name + "' is a derived name, not an input variable");
    auto it = vars.find(name); if (it != vars.end()) return it->second;
    return vars[name] = A.newVar(name);
  }

  // ---- expressions -----------------------------------------------------------
  int expr() {
    int l = term();
    while (isSym("+") || isSym("-")) { bool plus = isSym("+"); p++; int r = term(); l = A.mk(plus ? ADD : SUB, l, r); }
    return l;
  }
  int term() {
    int l = unary();
    while (isSym("*") || isSym("/")) { bool mul = isSym("*"); p++; int r = unary(); l = A.mk(mul ? MUL : DIV, l, r); }
    return l;
  }
  int unary() {
    if (isSym("-")) { p++; int x = unary(); return A.isNum(x) ? A.num(-A.n[x].val) : A.mk(NEG, x); }
    if (isSym("+")) { p++; return unary(); }
    return power();
  }
  int power() {
    int b = atom();
    if (isSym("^")) { p++; int e = unary(); return A.mk(POW, b, e); }
    return b;
  }
  int atom() {
    Tok k = t[p];
    if (k.k == Tok::NUM) { p++; return A.num(k.v); }
    if (isSym("(")) { p++; int e = expr(); expect(")"); return e; }
    if (k.k == Tok::ID) {
      p++;
      if (isSym("(")) {
        p++; string f = k.s;
        if (f == "d") {
          int e = expr(); expect(",");
          if (t[p].k != Tok::ID) fail("second argument of d() must be a variable name");
          int vi = varIndex(t[p].s); p++; expect(")");
          Differ df(A, vi); return df.D(e);
        }
        int a = expr(); expect(")");
        if (f == "sin") return A.mk(SIN, a);
        if (f == "cos") return A.mk(COS, a);
        if (f == "ln" || f == "log") return A.mk(LN, a);
        if (f == "exp") return A.mk(EXP, a);
        if (f == "sqrt") return A.mk(SQRT, a);
        if (f == "abs") return A.mk(ABS, a);
        p--; fail("unknown function '" + f + "'");
      }
      if (k.s == "pi") return A.num(M_PI);
      if (k.s == "e") return A.num(M_E);
      auto it = names.find(k.s); if (it != names.end()) return it->second;
      return A.var(varIndex(k.s));
    }
    fail("expected an expression");
  }

  // ---- statements -----------------------------------------------------------------
  double signedNum() {
    bool neg = false; if (isSym("-")) { neg = true; p++; }
    if (t[p].k != Tok::NUM) fail("expected a number");
    double v = t[p++].v; return neg ? -v : v;
  }
  void assume() {          // pass 1: constrain input variables
    p = 1;
    if (t[p].k != Tok::ID) fail("expected a variable after 'assume'");
    string name = t[p].s; p++;
    int vi = varIndex(name); Iv& v = A.varIv[vi];
    if (t[p].k == Tok::ID && t[p].s == "in") {
      p++; expect("["); double lo = signedNum(); expect(","); double hi = signedNum(); expect("]");
      if (lo > hi) fail("empty interval");
      v.lo = max(v.lo, lo); v.hi = min(v.hi, hi); if (lo > 0 || hi < 0) v.nz = true;
    } else {
      string op = t[p].s; if (t[p].k != Tok::SYM) fail("expected >, >=, <, <=, != or 'in'"); p++;
      double c = signedNum();
      if (c != 0 && op != "in") fail("only comparisons against 0 are supported (use 'in [a, b]' for ranges)");
      if (op == ">") { v.lo = max(v.lo, 0.0); v.nz = true; }
      else if (op == ">=") v.lo = max(v.lo, 0.0);
      else if (op == "<") { v.hi = min(v.hi, 0.0); v.nz = true; }
      else if (op == "<=") v.hi = min(v.hi, 0.0);
      else if (op == "!=") v.nz = true;
      else fail("unknown comparison '" + op + "'");
    }
    if (t[p].k != Tok::END) fail("unexpected input after assumption");
    if (v.lo > v.hi || (v.lo == 0 && v.hi == 0 && v.nz)) fail("assumptions on '" + name + "' are contradictory");
  }
  void statement() {       // pass 2
    p = 0;
    if (t[0].k == Tok::ID && t[0].s == "assume") return;
    if (t[0].k == Tok::ID && t[1].k == Tok::SYM && t[1].s == "=") {
      string name = t[0].s; p = 2;
      if (name == "pi" || name == "e" || name == "d") fail("'" + name + "' is reserved");
      if (vars.count(name)) fail("'" + name + "' is already used as an input variable");
      int e = expr(); if (t[p].k != Tok::END) fail("unexpected input after expression");
      names[name] = e; outs.push_back({name, e}); return;
    }
    int e = expr(); if (t[p].k != Tok::END) fail("unexpected input after expression");
    outs.push_back({"_" + to_string(++anon), e});
  }
  void parse(const string& src) {
    vector<string> lines; { stringstream ss(src); string l; while (getline(ss, l)) lines.push_back(l); }
    vector<vector<Tok>> toks;
    for (size_t i = 0; i < lines.size(); i++) toks.push_back(lexLine(lines[i], (int)i + 1));
    for (size_t i = 0; i < lines.size(); i++) {       // pass 1: assumptions
      t = toks[i]; ln = (int)i + 1;
      if (t[0].k == Tok::ID && t[0].s == "assume") assume();
    }
    for (size_t i = 0; i < lines.size(); i++) {       // pass 2: statements
      t = toks[i]; ln = (int)i + 1;
      if (t[0].k == Tok::END) continue;
      statement();
    }
    if (outs.empty()) raiseError("program has no expressions");
  }
};
