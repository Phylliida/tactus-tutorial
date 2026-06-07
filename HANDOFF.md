# Tactus Tutorial — Session Handoff

This document records what got built and what got discovered while writing the Tactus tutorial. The tutorial itself lives in `chapters/`; this is the meta-record for future sessions and for sharing back with Tactus upstream.

## ⚠️ Run everything with `--lean-backend`

As of 2026-06-06 the tutorial **must** be verified with the `--lean-backend`
flag:

```bash
../tactus/source/target-verus/release/verus --lean-backend <file>.rs
```

It routes exec fns through the Lean backend and keeps `uN → nat` casts as
`Clip{Nat}` for the Lean renderer. **Without it, `as nat` on spec-fn arguments
looks "dropped" (`gcd a b` with `a : Int`) and everything errors** — that's not a
bug, it's the wrong invocation (cost me a wrong-turn bug report this session; see
the deleted false-alarm note in the bug log below). All chapter READMEs + the
regression command now include the flag.

## What was built

### Eight tutorial chapters — all verifying clean (0 errors)

| Chapter | Topic | README | `.rs` | Verifies |
|---|---|---|---|---|
| 0 | Setup and toolchain | ✅ | reference doc | — |
| 1 | `sum_to_n` — closed-form identity proof + `sum_iter` exec fn | ✅ | ✅ | ✅ |
| 2 | Fibonacci identities — `fib_pos`, `sum_fib_identity`, bonus `fib_iter` exec | ✅ | ✅ (×2) | ✅ |
| 2.5 | (optional) Same Fibonacci theorems over `int` instead of `nat` | ✅ | ✅ | ✅ |
| 3 | Strong induction — `fib(n) ≤ 2ⁿ` and the addition formula | ✅ | ✅ | ✅ |
| 4 | `factorial` — iterative Rust verified against recursive `fact` spec | ✅ | ✅ | ✅ |
| 5 | `pow_by_squaring` — fast (O(log e)) exponentiation vs recursive `pow` ⭐ | ✅ | ✅ | ✅ |
| 6 | `gcd` — iterative Euclid vs recursive `gcd` (mod reasoning) ⭐ | ✅ | ✅ | ✅ |
| 7 | `fast_fib` — O(log n) fast-doubling Fibonacci ⭐ | ✅ | ✅ | ✅ |

All chapters 0–7 verify with **0 errors** under `--lean-backend`. (Do not track
exact "N verified" counts — they shift between Tactus versions; see "On
obligation counts" below.) Chapter 7 — the Fibonacci-thread capstone — is the
recursive `fast_fib(n) = (F(n), F(n+1))` verified end-to-end: both doubling
identities (from ch3's `fib_addition`), product-overflow safety, and `decreases`
termination.

The arc: induction-in-a-line (1) → strong induction (3) → iterative-vs-recursive
exec verification (1/2/4) → a *faster-than-its-spec* algorithm proven correct (5)
→ mod-reasoning where the spec **is** the loop step (6) → the O(log n) Fibonacci
that ch3's addition formula unlocks (7, in progress).

### One helper-lemma file

`lean-helpers/TactusTutorialHelpers.lean` — five `@[simp]` lemmas for the unconditional `.toNat` shapes that arise from Verus's `(n - 1) as nat` casts. Symlinked into `tactus/lean-project/`; the lakefile was extended with a `lean_lib TactusTutorialHelpers` target. Used by chapter 2.

### Top-level README

Includes a "note on simp" section explaining the convention (no intermediate `simp`; `simp only [pinned_list]` is fine; bare `simp` only as a closer).

## On obligation counts (important)

The `verification results:: N verified, 0 errors` count is **volatile across Tactus
versions** — it drifted twice in development (e.g. `sum_to_n` 9→6 after the
friction-1/2 lowering fixes changed internal obligation bookkeeping). The READMEs
therefore write expected output as `N verified, 0 errors` and a one-time note (ch0,
"Reading verification output") explains that only `0 errors` is meaningful. **When
checking chapters, assert on `0 errors`, never on a specific number.**

## Bugs filed during this work

Each was filed as `BUG-*.md` at the `verus-cad/` repo root; some were removed after fix.

| Bug | Status |
|---|---|
| `as nat` cast dropped for U → Nat | **FIXED** (the Clip emission was elided) |
| Mathlib imports not threaded to exec fn theorems | **FIXED** (`nlinarith` etc. now available in exec contexts) |
| FileLoader scanner confused by `by`+`{` across `//` comment lines | **FIXED** |
| Multi-var loop variable names alpha-renamed | **FIXED** |
| Helper proof fn invocation from exec body | **FIXED** for Lean-syntax `have _ := fn args` |
| Synthetic temp `let tmp__1 := x` blocks asserted bounds | **FIXED** (`simp_all <;> omega` rung) |
| Ch5 friction 1 — loop invariant arrives as one unsplit `∧` hypothesis | **FIXED** (now individual hyps) |
| Ch5 friction 2 — ℤ-vs-ℕ inconsistent lowering of `(x as nat)` | **FIXED** (lowers consistently) |
| Spec/proof fn `decreases` with a **mod** measure (`a % b < b`) fails termination (blocked ch6 gcd) | **FIXED** 2026-06-06 (tactus `9eebbbb`/`d33f3a9`; `decreasing_by` now `first \| omega \| (apply Nat.mod_lt <;> omega) \| decreasing_tactic`). `BUG-spec-fn-decreases-mod-termination.md` |
| Under `--lean-backend`, the aggregate `main.lean` dropped the source `import Mathlib.Tactic.Linarith` → `nlinarith` "unknown tactic" (broke ch1/3/4/5 etc.) | **FIXED** 2026-06-06 (tactus `f949022`; `krate_preamble` unions imports over emitted fns). `BUG-lean-backend-main-lean-drops-mathlib-import.md` |
| ~~`as nat` coercion dropped on spec-fn args under the rebuild~~ | **NOT A BUG** — was running *without* `--lean-backend`. False alarm; report deleted. The lesson: always pass `--lean-backend` (see top of this file). |

This was a remarkably fast feedback loop — every report got a fix within hours. The
tutorial (especially the chapter-5/6 capstones) would not exist without it.

## Bugs still open

1. **Dep-walker over-inclusion + order** in proof-fn → proof-fn calls. `BUG-proof-fn-dep-walker-over-includes.md`. Workaround: keep every proof fn self-contained (self-recursion is fine; don't call sibling proof fns — call them from the exec fn instead, which works).
2. **Ch5 friction 3** — `e.toNat`-vs-`e` cast noise in unfolded recursive indices, and the **variable-range bounds** (`0 ≤ x ∧ x < 2⁶⁴`) arriving as conjunctions (unlike the now-split invariant). Both worked around author-side in chapter 5; documented in `BUG-ch5-pow-iter-lowering-frictions.md` (marked RESOLVED for frictions 1/2, with these two as future-polish candidates that would let the ch5 proof shrink).
3. **`omega` doesn't traverse into function arguments.** Mathlib-side, not Tactus.
4. **`proof { fn_name(args); }` Verus-syntax** gives "unknown tactic"; workaround `proof { have _ := fn_name args }`.
5. **`invariant P by { tac }`** per-obligation surface syntax not supported (`Wp::AssertByTactus` exists internally per DESIGN.md).

## Techniques future tutorial writers should know

### `simp only` over `simp` (the robustness rule)

Bare `simp`/`simp_all` shouldn't appear as an *intermediate* step — Mathlib's `@[simp]` set evolves. Use `simp only [pinned_list]` (stable), or `rw [if_neg …]` / `rw [if_pos …]` to step through definitions, and reserve bare `simp` for the *closing* tactic only. All chapters follow this strictly. (The chapter READMEs were resynced this session — they had been showing pre-refactor intermediate-`simp` proofs that no longer matched the `.rs`.)

### The `rw [show ... toNat ... from by omega]` idiom

For `.toNat` cleanups from `(n - 1) as nat` casts: inline `rw [show <messy> = <clean> from by omega]` for conditional shapes; the `TactusTutorialHelpers` `@[simp]` lemmas for the unconditional ones (fired via `simp only [...]`).

### Self-recursive proof fns for strong induction

`proof fn foo(n: nat) ... decreases n by { if h : n = 0 then (...) else ( have ih := foo (n - 1) ... ) }`. Keep them self-contained (don't call sibling proof fns — dep-walker bug). The exec fn *can* call them (`have h := foo args`).

### Exec-fn verification: invariant + assert chain + closer

The chapter-4/5 template for "iterative loop vs recursive spec":
- A **recurrence-based invariant** (`result == fact(i)`, or `result * pow(b,e) == pow(base,exp)`).
- Per-step **`assert(...) by { ... }`** blocks that feed the maintain step (unfold the spec one level, rewrite via the crux lemma) and the overflow bound.
- A **whole-fn closer** for the obligations the default ladder can't reach.

Closer forms seen:
- `sum_iter` (ch1): `first | tactus_auto | (intros; nlinarith)` suffices — its invariant is a *closed form* (`2*result == i*(i+1)`), pure polynomial arithmetic. (The three inline asserts it once had were vestigial workarounds and were removed.)
- `pow_iter` (ch5): `first | tactus_auto | (intros; omega) | (intros; nlinarith)`. **`omega` bridges ℕ/ℤ** (loop vars are `u64`/ℤ, spec fns are `nat`/ℕ) and abstracts nonlinear products as opaque atoms, so it closes the linear/overflow obligations; `nlinarith` handles the genuinely nonlinear ones.

### The crux lemma pattern (ch5 `pow_square`)

A fast algorithm usually has one key identity the loop turns on. For squaring it's `pow(b*b, k) == pow(b, 2k)` — proved by induction on `k`, unfolding the LHS once and the RHS twice and bridging with the IH (`ring` finishes). Isolate that lemma; the loop body then just rewrites `pow(b, e)` ↔ `pow(b*b, e/2)` each step.

### Overflow lower bounds need explicit nonneg asserts (ch5)

The variable-range facts (`0 ≤ x ∧ x < 2⁶⁴`) come as conjunctions that `nlinarith` won't split, so the overflow check's *lower* bound `0 ≤ b*b` fails. Fix: `assert(0 <= b * b) by { intros; have hb : 0 <= b := by omega; nlinarith [hb] }` — `omega` extracts the nonneg from the conjunction, `nlinarith` does the product.

## What this session validated about Tactus

The headline DESIGN.md use case — "verify Rust against recursive math specs" — works end-to-end, **including faster-than-spec algorithms**. Chapter 5 is the proof: a real `u64` exponentiation-by-squaring loop (O(log e)) verified against the O(e) recursive `pow`, with overflow safety — exactly the "prove once, optimize freely" promise. Chapters 1/2/4 cover the linear/closed-form cases; chapter 5 is the capstone.

## Setup the next session should do first

1. Confirm Tactus builds (`cd tactus/source && vargo build --release`) — expect `0 errors` on vstd (count ~1530, may vary).
2. Confirm the `TactusTutorialHelpers` symlink exists and `lake build TactusTutorialHelpers` succeeds (one-time per Tactus rebuild that wipes `lean-project/.lake/`).
3. Run the regression below — every chapter file should end with `0 errors`.

## Regression check

```bash
for f in chapters/*/*.rs; do
  echo "=== $f ==="
  PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH" \
    ../tactus/source/target-verus/release/verus --lean-backend "$f" 2>&1 | tail -1
done
```

Note the **`--lean-backend`** flag — required (see top of this file).

Expected: every line ends with `0 errors` (the `N verified` number is not meaningful — see "On obligation counts").

Last full regression: chapters 0–7 (9 `.rs` files: 1, 2×2, 2.5, 3, 4, 5, 6, 7),
all **0 errors** under `--lean-backend`, 2026-06-07.

## Next steps

1. **Combinatorial identities** — Pascal's rule, binomial theorem, hockey stick
   (the Sage-flavored direction; needs a binomial-coefficient spec; proof-fn-first,
   closer to ch3). Verifiable-friendly (subtraction measures, no exec recursion).
2. **Matrix-power Fibonacci** (the ch7 exercise) — unifies fast-doubling with
   ch5's exponentiation-by-squaring via `[[1,1],[1,0]]^n`.

## Techniques discovered building chapters 6–7

### `--lean-backend` cast bridges (ch4/6/7)

When an `nlinarith`/`linarith` over a spec-fn value fails under `--lean-backend`,
add `have h : <var> = (<spec expr> : Int) := by omega` (and lift any ℕ bound
chain to ℤ the same way) before the nonlinear tactic. ch4's two exec asserts and
ch7's identity asserts all use this.

### Naming synthetic goal-position lets in pre-loop / before-call asserts (ch2/4/7)

The loop-local-names lowering puts a fn's init/temp values (`let result := 1;
let i := 0; …`, `let k := n/2; …`) in **goal position**, *not* auto-intro'd. A
plain `intros` then introduces them with **inaccessible** names, so referencing
`i` / `k` by name fails ("Unknown identifier"). Two fixes, depending on the
assert:
- **Name them explicitly:** `intro _ a b i` (the leading `_`s are any guard
  hyps like `¬(n = 0)` / `2 ≠ 0` that precede the lets). Used in ch2 `fib_iter`
  (`intro _ a b i`) and ch7's recursive-call bound (`intro _ _ _ _ k`).
- **Or avoid naming:** `show <concrete goal>` strips the lets by defeq, then
  evaluate. Used in ch4's entry assert (`show Int.toNat 1 = fact (Int.toNat 0)`).
Note the `--` (not `//`) for comments *inside* `by { … }` Lean blocks.

### `omega` vs `nlinarith` on `fib`-product goals (ch7)

`F(2k+1) = a²+b²` closes with **`omega`** (it atomizes the `↑fib·↑fib` products
and reads the lifted addition-formula identity linearly); `F(2k)`/`F(2k+2)`
genuinely expand `a·(2b−a)`, so they need **`nlinarith`**. Using `nlinarith` for
the former whnf-loops on the noncomputable `fib`. ch7 also raises `heartbeats`
(the whole-fn proof is large — many asserts over a deep let context).

### Tactus bugs surfaced + fixed this arc

`BUG-spec-fn-decreases-mod-termination` (gcd's `a % b < b`), the `--lean-backend`
`main.lean` Mathlib-import drop, and `BUG-tuple-destructure-alias-temps-block-omega`
(fast_fib's tuple destructure) were all reported and fixed upstream — see the
`verus-cad/` repo root.
