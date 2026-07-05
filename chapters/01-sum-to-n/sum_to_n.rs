// Chapter 1: sum_to_n
//
// Prove that 1 + 2 + ... + n == n*(n+1)/2.
// To avoid integer division, we prove the equivalent identity:
//
//     2 * sum_to(n) == n * (n + 1)
//
// The interesting part is `sum_formula`: the proof closes in one
// `induction` tactic. Z3 cannot do this without manually unfolding
// the recursion and supplying ladder lemmas.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

// -------- The specification ------------------------------------------------
//
// `spec fn` is a *mathematical* function. It's used only in proofs and
// specs — never compiled to runtime code. Recursion needs `decreases` so
// the kernel can check termination.

spec fn sum_to(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { (n + sum_to((n - 1) as nat)) as nat }
}

// -------- Warm-up: concrete values ----------------------------------------
//
// Before doing induction, sanity-check that `sum_to` behaves as expected
// on small inputs. `unfold` exposes the body of the recursive definition;
// `simp` and `decide` then close the goal.

proof fn sum_zero()
    ensures sum_to(0) == 0
by {
    unfold sum_to
    decide
}

proof fn sum_three()
    ensures sum_to(3) == 6
by {
    -- One `unfold` per level of recursion. `decide` then computes
    -- the concrete value. (We avoid `repeat (unfold sum_to; simp)`
    -- — simp is governed by Mathlib's evolving `@[simp]` set and
    -- shouldn't appear between tactics that depend on its output.)
    unfold sum_to
    unfold sum_to
    unfold sum_to
    unfold sum_to
    decide
}

// -------- The main theorem ------------------------------------------------
//
// One `induction` tactic, two cases.
//
//   - `zero` case: sum_to(0) = 0, so 2*0 == 0*(0+1).  Definitional.
//   - `succ k ih` case: with `ih : 2 * sum_to(k) == k * (k+1)` in scope,
//     prove 2 * sum_to(k+1) == (k+1) * (k+2). Unfolding sum_to and
//     substituting the induction hypothesis is a polynomial identity
//     — `nlinarith` (from Mathlib) handles it.

proof fn sum_formula(n: nat)
    ensures 2 * sum_to(n) == n * (n + 1)
by {
    induction n with
    | zero => unfold sum_to; decide
    | succ k ih =>
        unfold sum_to
        -- Eliminate the `if k + 1 == 0 then 0 else …` branch (the
        -- condition is false). `rw [if_neg …]` is preferable to a bare
        -- `simp` here: `simp` is governed by Mathlib's evolving
        -- `@[simp]` set, so a future Mathlib update could change what
        -- shape it leaves the goal in. `if_neg` is a stable core lemma.
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]
        nlinarith [ih]
}

// -------- Iterative implementation ----------------------------------------
//
// Now the headline Tactus use case: a real Rust function with a loop,
// verified against the *mathematical* identity we just proved.
//
// `sum_iter(n)` computes 0 + 1 + … + n by accumulating into `result`.
// The postcondition `2 * r == n * (n + 1)` is the same closed form we
// proved equivalent to `sum_to(n)` above.
//
// The loop **invariant** captures what's true at every iteration:
// `2 * result == i * (i + 1)`. The loop maintains it; at exit `i == n`,
// giving us the postcondition. The **decreases** clause `n - i` proves
// termination — it strictly decreases on each iteration.
//
// Some obligations need help beyond the default closer (`rfl | decide |
// omega | simp_all | …`): the loop-invariant maintain step and the
// postcondition both involve *nonlinear* arithmetic (the product
// `i * (i + 1)`), which `omega` can't handle. We discharge exactly those
// steps with the fixed-menu `by(nonlinear_arith)` selector (Verus-native;
// maps to Lean `nlinarith`) placed at the precise site — the invariant
// algebra stated for the *next* state just before we mutate, and the
// substitution `i == n` after the loop. The default `tactus_auto` closes
// everything else, so no whole-fn closer override is needed.

#[verifier::tactus_auto]
fn sum_iter(n: u64) -> (r: u64)
    requires n <= 1000
    ensures 2 * r == n * (n + 1)
{
    let mut result: u64 = 0;
    let mut i: u64 = 0;
    while i < n
        invariant
            i <= n,
            n <= 1000,
            2 * result == i * (i + 1),
            // Bound `result` so the overflow check on `result + i` closes
            // without re-deriving the closed-form maximum each time:
            result <= 1001 * 1001,
        decreases n - i
    {
        // Invariant maintenance here is *nonlinear* (the product `i * (i + 1)`),
        // which the default closer's `omega` / `simp_all` can't reach. Rather
        // than override the whole-fn closer with a raw tactic string, we place
        // the fixed-menu `by(nonlinear_arith)` selector (Verus-native; maps to
        // Lean `nlinarith`) on exactly the two nonlinear steps, stated for the
        // *next* state before mutating. `tactus_auto` then closes the invariant
        // from these facts plus the assignment equalities.
        assert(2 * (result + (i + 1)) == (i + 1) * (i + 2)) by(nonlinear_arith)
            requires 2 * result == i * (i + 1);
        assert(result + (i + 1) <= 1001 * 1001) by(nonlinear_arith)
            requires 2 * result == i * (i + 1), 0 <= i, i < n, n <= 1000;
        i = i + 1;
        result = result + i;
    }
    // Exit: `i == n` (from `i <= n` and the failed loop test), so substitute it
    // into the nonlinear invariant to land the postcondition.
    assert(2 * result == n * (n + 1)) by(nonlinear_arith)
        requires 2 * result == i * (i + 1), i == n;
    result
}

fn main() {}

} // verus!
