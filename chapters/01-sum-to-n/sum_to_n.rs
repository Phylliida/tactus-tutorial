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
    simp
}

proof fn sum_three()
    ensures sum_to(3) == 6
by {
    unfold sum_to
    simp
    unfold sum_to
    simp
    unfold sum_to
    simp
    unfold sum_to
    simp
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
    | zero => unfold sum_to; simp
    | succ k ih => unfold sum_to; simp; nlinarith [ih]
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
// Three things make this work:
//   - The loop **invariant** captures what's true at every iteration:
//     `2 * result == i * (i + 1)`. The loop maintains it; at exit
//     `i == n`, giving us the postcondition.
//   - The **decreases** clause proves termination: `n - i` strictly
//     decreases on each iteration.
//   - The `tactus_tactic` attribute extends the default closer with
//     `intros; nlinarith` so the polynomial maintain step
//     (`2 * (result + (i+1)) == (i+1) * (i+2)`) can close.
//
// Without `nlinarith` we'd be stuck — `omega` handles linear
// arithmetic only, and the maintain step is genuinely nonlinear
// (it has a product of unknowns).

#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; nlinarith)")]
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
            // Bound `result` so the auto-tactic can discharge overflow
            // on `result + i` without needing the closed-form maximum:
            result <= 1001 * 1001,
        decreases n - i
    {
        i = i + 1;
        result = result + i;
    }
    result
}

fn main() {}

} // verus!
