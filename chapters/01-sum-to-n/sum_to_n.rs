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

fn main() {}

} // verus!
