# Tactus Tutorial — Session Handoff

This document records what got built and what got discovered while writing the Tactus tutorial. The tutorial itself lives in `chapters/`; this is the meta-record for future sessions and for sharing back with Tactus upstream.

## What was built

### Five tutorial chapters (all verifying clean)

| Chapter | Topic | Result |
|---|---|---|
| 0 | Setup and toolchain | Reference doc — no `.rs` |
| 1 | `sum_to_n` — closed-form identity proof + `sum_iter` exec fn | 9 verified |
| 2 | Fibonacci identities — `fib_pos`, `sum_fib_identity`, plus bonus `fib_iter` exec | 9 verified |
| 2.5 | (optional) Same Fibonacci theorems encoded over `int` instead of `nat` | 7 verified |
| 3 | Strong induction — `fib(n) ≤ 2ⁿ` and the addition formula | 7 verified |
| 4 | `factorial` — iterative Rust verified against recursive math spec | 9 verified |

Total: 41 verification obligations across 5 chapters, 0 errors.

### One helper-lemma file

`lean-helpers/TactusTutorialHelpers.lean` — five `@[simp]` lemmas for the unconditional `.toNat` shapes that arise from Verus's `(n - 1) as nat` casts. Symlinked into `tactus/lean-project/`; the lakefile was extended with a `lean_lib TactusTutorialHelpers` target. Used by chapter 2.

### Top-level README

Includes a "note on simp" section explaining the convention (no intermediate `simp`; `simp only [pinned_list]` is fine; bare `simp` only as a closer).

## Bugs filed during this work

In rough order. Each was filed as `BUG-*.md` at the `verus-cad/` repo root; some have been removed after fix but are listed here for the record.

| # | Bug | Status |
|---|---|---|
| 1 | `as nat` cast dropped for U → Nat | **FIXED** (Tactus-side, the Clip emission was elided) |
| 2 | Mathlib imports not threaded to exec fn theorems | **FIXED** (`nlinarith` etc. now available in exec contexts) |
| 3 | FileLoader scanner gets confused by `by` followed by `{` across `//` comment lines | **FIXED** |
| 4 | Multi-var loop variable names alpha-renamed | **FIXED** (single-var was fixed first, then multi-var followup) |
| 5 | Helper proof fn invocation from exec body | **FIXED** for Lean-syntax `have _ := fn args`; Verus-syntax `fn(args);` still doesn't work (see "remaining" below) |
| 6 | Synthetic temp `let tmp__1 := x` blocks asserted bounds | **FIXED** (`simp_all <;> omega` rung added to default closer) |

This was a remarkably fast feedback loop — every report I filed got a fix within hours. The tutorial would not have existed without this; six of the chapters' eight core techniques were unblocked by these fixes.

## Bugs still open after end-of-session audit

I tested each remaining issue from my earlier UX review and found these are the four that genuinely persist:

1. **Dep-walker over-inclusion + order** in proof-fn → proof-fn calls. Bug report at `BUG-proof-fn-dep-walker-over-includes.md` — newest as of session end.
2. **`omega` doesn't traverse into function arguments.** Mathlib-side improvement, not Tactus.
3. **`proof { fn_name(args); }` Verus-syntax** still gives "unknown tactic". Inconsistency with Verus convention; workaround is `proof { have _ := fn_name args }`.
4. **`invariant P by { tac }`** per-obligation surface syntax not supported. `Wp::AssertByTactus` exists internally per DESIGN.md.

Issues that **were fixed** during the session and should NOT be re-reported:

- Error location pointing at fn signature instead of failing tactic line ← FIXED
- Multi-var loop variable alpha-renaming ← FIXED
- Zero-arg proof fns getting a phantom Int parameter ← FIXED
- The `// in tactic block` FileLoader scanner cross-contamination ← FIXED
- `// vs --` diagnostic exists (though it suggests `Nat.div` even when the user clearly meant a comment — minor improvement opportunity, see UX review)

## Techniques discovered that future tutorial writers should know

### The `rw [show ... toNat ... from by omega]` idiom

For conditional `.toNat` rewrites (e.g., `((↑n : Int) - 1).toNat = n - 1` requiring `n ≥ 1`), inline `rw [show … from by omega]` is the standard form. The TactusTutorialHelpers file handles the *unconditional* cases (`((↑(k + 1) : Int) - 1).toNat = k` and friends) via `@[simp]`. The conditional ones can't be simp-tagged (Lean's simp doesn't auto-supply hypotheses) and stay inline.

### Self-recursive proof fns for strong induction

`proof fn foo(n: nat) ... decreases n by { ... if h : n = 0 then (...) else ( ... have ih := foo (n - 1) ... ) }`. The recursive call gives you the IH at the smaller value. Cross-fn calls aren't yet smooth (see open bug), so each strong-induction proof should be self-contained — inline any helpers rather than splitting into separate proof fns.

### The closed-form invariant trick

When verifying iterative-vs-recursive specs, prefer a closed-form invariant where possible. `sum_iter` works cleanly because the invariant is `2 * result == i * (i + 1)` — pure arithmetic, omega handles it. `fact_iter` needs a recurrence-based invariant `result == fact(i)`, which requires unfolding fact at each iteration plus monotonicity for the overflow bound. The latter is doable (see chapter 4) but ~3x the proof length.

### Loop-body assert chains for exec fn verification

Inside `tactus_auto` loops, the pattern is:

```rust
while i < n
    invariant ..., result == fact(i as nat), result <= BOUND
    decreases n - i
{
    assert(recurrence) by { ... };       // fact(i+1) = (i+1) * fact(i)
    assert(bound) by { ... };             // (i+1) * result <= BOUND
    assert(new_invariant) by { ... };     // result * (i+1) = fact((i+1))
    result = result * (i + 1);            // overflow check uses asserted bound
    i = i + 1;
}
```

The recurrence is needed to relate the new state to the spec. The bound is needed for the overflow check. The new-invariant assert bridges the maintain step (since `omega` doesn't combine multiplication with spec-fn equality).

After the synthetic-temp closer fix, the overflow check uses the asserted bound directly — that was the killer block before.

### `simp only` over `simp`

Bare `simp` shouldn't appear in the middle of a proof because Mathlib's `@[simp]` set evolves. `simp only [list_of_pinned_lemmas]` is stable. Bare `simp` only as a closing tactic is fine. Chapters 1–4 follow this rule strictly.

## What this session validated about Tactus

The headline use case from DESIGN.md — "verify Rust code against recursive math specs" — works end-to-end after the fixes that landed. Chapter 4's `factorial` is the proof: a real `u64` Rust function with a multiplicative loop, verified against the recursive `fact` spec, with overflow safety. The proof is ~150 lines including three helper proof fns (recurrence, monotonicity, concrete bound) and three inline asserts per loop iteration. Readable; teaches a technique; verifies in ~30 seconds.

For anyone writing additional chapters (factorial → pow_by_squaring → gcd → insertion sort → …), chapter 4's structure is the template.

## Setup the next session should do first

1. Confirm Tactus builds (`cd tactus/source && vargo build --release`) — expect "1530 verified, 0 errors" on vstd.
2. Confirm the TactusTutorialHelpers symlink exists and `lake build TactusTutorialHelpers` succeeds (one-time per Tactus rebuild that wipes `lean-project/.lake/`).
3. Run the regression check: every chapter file from this session should still verify. See "All chapter files verify" below.

## All chapter files verify

```bash
for f in chapters/*/*.rs; do
  echo "=== $f ==="
  PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH" \
    ../tactus/source/target-verus/release/verus "$f" 2>&1 | tail -1
done
```

Expected output: every line ends with `verification results:: N verified, 0 errors`.

Last verified: end of this session, post-simp-refactor commit (`612e600`).
