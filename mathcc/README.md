# mathcc — a guarded, certificate-checked compiler for mathematical expressions

A compiler (C++17, ~1,500 lines, no dependencies) that takes mathematical expressions with
optional domain assumptions, simplifies them **symbolically without changing their IEEE‑754
meaning**, and emits fast code (register VM or C).

```
make            # builds bin/mathcc
make test       # 27 golden/behaviour tests + a random-expression soundness fuzzer
./bin/mathcc examples/demo.mc --tac --cert --verify 20000 --bench 3000000
./bin/mathcc examples/stable.mc --stable
./bin/mathcc --discover
```

## Web workbench (frontend) — no backend needed

`site/index.html` is **one self-contained file**: the interface, the examples and the compiler itself, built to
WebAssembly from the same C++ source. Open it in a browser (double-click) or host it on any static host
(GitHub Pages, Netlify, an artifact link). It makes **zero network requests**; the compiler runs in a Web Worker.

```
python3 -m http.server -d site       # or just open site/index.html
```
Rebuild it after changing the C++ (needs the WASI SDK, https://github.com/WebAssembly/wasi-sdk/releases):
```
make site WASI_SDK=/path/to/wasi-sdk       # clang --target=wasm32-wasi, then web/build_site.py inlines everything
```
There is also a server variant (`make web` → `web/server.py`, Python standard library) that runs the native binary;
both use the same page (`web/static/index.html`). The WebAssembly build and the native binary produce byte-identical reports.

The site has five pages (hash-routed, so it still works as a single file): **Home**, **Workbench**, **What is new**
(explains the four contributions, with a diagram and a comparison with prior work), **References** (the papers and
books that shaped the design, with what was taken from each) and **About** (author, registration number, phases, how
it is built). The header carries the project name, Shaurya Sharma and Reg. No. 24BDS0194.

The Workbench has an editor with error-line highlighting, a policy switch (guarded / conservative / classic-unsafe)
and five tabs: Rewrites (original struck through, simplified result, guard badges, and a **Why?** panel that explains
every rewrite step in plain English: which rule fired, which condition it needs, and whether that condition was proven
or is checked at run time; skipped rewrites are explained too), Generated code, Correctness, Speed and Rule discovery.
`./bin/mathcc file.mc --why` prints the same explanation on the command line. The page opens with an animation of
crossed-out rewrites being blown away (Skip or Esc ends it; off when the browser asks for reduced motion).

## The idea in one paragraph

Every computer algebra system rewrites `x/x` to `1`, `sqrt(x^2)` to `x`, `sqrt(z)*sqrt(z)` to `z`.
All three are **wrong** for some inputs (`x=0`, `x<0`, `z<0`). `mathcc` attaches a *side condition
(guard)* to each such rewrite. A guard is (1) **proven at compile time** from your assumptions by an
interval + definedness analysis, so it costs nothing; otherwise (2) **checked at run time** – the guard
becomes an extra output of the compiled program and the generated code **falls back to the original
expression** when it fails; or (3) the rewrite is **skipped** (conservative mode / provably false).
The result is code that is *faster than the original and bit-for-bit meaning-preserving*, including at
the singular points (`NaN` where the original is `NaN`).

## Four novelty components

| # | Component | What it does | Where |
|---|-----------|--------------|-------|
| 1 | **Guarded rewriting with static discharge and run-time fallback** | Guards `x≠0`, `x>0`, `x≥0`, `finite(x)` on *any sub-expression* (e.g. `w+1 ≠ 0`); discharged by interval/definedness analysis, else emitted as a cheap check with fallback to the original | `simplify.hpp`, `backend.hpp` |
| 2 | **Self-auditing rewrites (certificates)** | Every rewrite is logged as `(before, after, guards)`. An independent checker re-samples inputs satisfying the guards and checks `before == after` (NaN‑aware). It also hunts for a **counterexample with the guard removed**, proving each run-time guard is *necessary* (e.g. `guard [x != 0] dropped → gives 0, original gives nan`) | `analysis.hpp: certify` |
| 3 | **Stability-aware selection** | Generates accuracy-improving equivalents (`1-cos x → 2sin²(x/2)`, `exp x−1 → expm1`, `ln(1+x) → log1p`, `√u−√v → (u−v)/(√u+√v)`), measures max relative error against a long‑double reference, and keeps the better form by (error, cost) | `simplify.hpp: stab`, `analysis.hpp: measuredError` |
| 4 | **Rule discovery with inferred side conditions** | Enumerates ~18k expressions, groups them by behaviour on sample points restricted to a region (`all`, `x≠0`, `x≥0`, `x>0`, `x<0`), reports identities the simplifier does *not* know together with the region where they hold, and re‑tests each on fresh points | `analysis.hpp: discoverRules` |

Supporting engineering: hash-consed DAG IR (free common-subexpression elimination, O(1) structural
equality), canonical sum/product forms, symbolic differentiation `d(expr, x)`, strength reduction
(`x^n` → square‑and‑multiply, `x^-1` → division, `x^0.5` → `sqrt`), numerator/denominator codegen,
value numbering, C emitter.

### Measured results (this machine, `examples/demo.mc`)

* **Soundness:** guarded mode – 0 mismatches vs. the original on 20,000 points per expression, and
  5,000+ random fuzz expressions on the final build (about 12,000 over development). The same inputs through the *unguarded* "classic" mode
  (`--mode unsafe`) give **339 / 9,831 / 286 wrong results** for `x*x/x`, `sqrt(z)*sqrt(z)`, `(w+1)/(w+1)`.
* **Certificates:** 12/12 rewrite steps verified; 3/3 conditional steps have a concrete counterexample
  when the guard is removed.
* **Speed (ns/eval, tree-walk → compiled):** `sin²+cos²+y/y` 122 → 4.4 (**28×**), `sqrt(x²)` 61 → 13,
  `d/dx(x³ sin x)` 188 → 70, `x*x/x` 17 → 6.0. Expressions whose guard fails half the time
  (`sqrt(z)*sqrt(z)`, z unconstrained) are not faster – the cost of the check plus fallback is real.
* **Accuracy (`--stable`):** `1−cos x` max rel. error 1e‑4 → 5e‑8, `exp x−1` 7e‑11 → 5e‑14,
  `ln(1+x)` 1e‑10 → 5e‑14, `√(x+1)−√x` 2.8e‑14 → 2.9e‑16 (limited by the long-double reference).

## Compiler phases (mapping to the course)

| Phase | Implementation |
|-------|----------------|
| Lexical analysis | `frontend.hpp: lexLine` – numbers, identifiers, `>= <= !=`, comments; errors with line/column (`--tokens` dumps tokens) |
| Syntax analysis | recursive descent, precedence `+ - < * / < unary - < ^` (right-assoc), function calls, `d(e, x)` |
| Semantic analysis | symbol table of inputs vs derived names, reserved names, assumption checking (contradictions rejected) |
| Intermediate representation | hash-consed expression DAG with an abstract domain per node (interval, zero-excluded, definitely-finite) |
| Optimization | guarded simplifier (canonical sums/products, merging exponents, trig/log/exp identities, `abs` resolution), CSE, strength reduction, stability rewrites |
| Code generation | three-address code (`--tac`), register VM, C source (`--emit-c`) |
| Run time | VM + guard checks + fallback |

## Input language

```
assume y > 0            # also >=, <, <=, !=, and:  assume x in [1, 10]
a = (x*x)/x             # named output (also usable in later lines)
d(x^3*sin(x), x)        # symbolic derivative, then simplified
```
Operators `+ - * / ^`; functions `sin cos ln log exp sqrt abs`; constants `pi`, `e`.
Variables that are never assigned are inputs.

## Semantics contract (read this before claiming anything)

The compiled result equals the original expression evaluated in IEEE‑754 double precision, with these
**explicit, documented exceptions**:

1. Inputs are finite numbers; overflow of `+ − ×` is ignored (overflow of `exp` is tracked).
2. `+0` and `−0` are identified, so the *sign* of an infinity produced by dividing by an exact zero may
   differ.
3. Equivalent forms may differ by a few ulps (`x/y` vs `x·y⁻¹`, `x³` as multiplications); `NaN` vs `±inf`
   on a domain boundary (`ln(0)` vs `ln(−1e‑16)`) is treated as equal by the verifier.
4. `x^0.5` is defined as `sqrt(x)` (C's `pow(−∞, 0.5)` returns `+∞`).
5. Verification skips points where the *original* expression is itself numerically unstable
   (`cos(exp(30))`), because rewriting legitimately changes the result there.

Bugs the fuzzer found and that are now fixed (useful viva material): unconditional merging of
fractional exponents was unsound at `−∞`; `build()` dropped factors when a coefficient became 0
(`0·ln z` → `0` even for `z<0`); `ln(exp y) → y` also needs `exp y` not to over/underflow;
`x/x` as `x·(1/x)` is not exactly 1 in floating point.

## Related work and an honest novelty statement

* **Guarded expressions in CAS** exist: REDUCE's GUARDIAN package computes degenerate cases as guarded
  expressions (Dolzmann & Sturm). Maple/Mathematica support `assume`. They stay symbolic; they do not emit
  executable code with run-time guard-and-fallback.
* **Herbie / egglog / Ruler**: Herbie improves floating-point accuracy by equality saturation, its rewrite
  rules were historically unsound, and egglog's interval analysis was used to make division rewrites sound;
  Ruler infers rewrite rules. Your component 3 and 4 are in this space — *not* new as ideas.
* **What is distinctive here** is the *combination* in one small compiler: static discharge by an
  interval+definedness domain → run-time guard with fallback to the original → per-step independent
  certificate with guard‑necessity counterexamples → NaN-exact verification, plus condition inference for
  discovered rules. A defensible claim is "a sound-by-construction expression compiler with checkable
  rewrite certificates", suited to a workshop paper or arXiv preprint, **not** a guaranteed patent.
  Software patentability depends on jurisdiction (in India, "computer programs per se" are excluded) and
  needs a prior-art search by a patent attorney.

References: Dolzmann & Sturm, *GUARDIAN: Guarded Expressions in Practice* (REDUCE manual §20.27);
Panchekha et al., *Herbie* (PLDI 2015); Willsey et al., *egg* (POPL 2021); Nandi et al., *Rewrite Rule
Inference Using Equality Saturation* (OOPSLA 2021); Zhang et al., *Better Together: Unifying Datalog and
Equality Saturation* (PLDI 2023) arXiv:2304.04332.

## Known limitations / future work

* No expansion/factoring (`(x²−1)/(x−1)` is not simplified) – needs polynomial arithmetic.
* Certificates are *randomised* checks (strong evidence, not a formal proof). Next step: discharge each
  step with an SMT solver (Z3) or export to Lean/Coq.
* Stability selection compares two candidates; a full e-graph with cost-based extraction would explore more.
* Rule discovery uses one variable and depth‑2 expressions; Ruler-style e-graph pruning would scale it.
* Error is measured empirically (long double reference), not bounded statically.

## Viva cheat-sheet

* *Why is `x/x → 1` unsound?* At `x=0` the original is `NaN`; the rewrite returns 1 – it changes a
  program's behaviour. Hence the guard `x ≠ 0`.
* *Why a DAG and not a tree?* Hash-consing gives CSE, O(1) equality, memoised simplification (linear time).
* *How are guards decided?* Interval `[lo,hi]` + "zero excluded" + "definitely finite" per node;
  `proven → free`, `refuted → skip`, `unknown → runtime check + fallback`.
* *Why fallback to the original?* It guarantees equality everywhere with zero risk; the fast path is only used
  where its side conditions hold.
* *How do you know rewrites are right?* Independent certificate checker + 5,000 fuzz expressions + the
  guard‑necessity counterexamples + the unsafe-mode comparison.
