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
    | zero => unfold sum_to; decide
    | succ k ih =>
        unfold sum_to
        -- Eliminate the `if k + 1 == 0 then 0 else …` branch (the
        -- condition is false). `rw [if_neg …]` is preferable to a bare
        -- `simp` here: `simp` is governed by Mathlib's evolving
        -- `@[simp]` set, so a future Mathlib update could change what
        -- shape it leaves the goal in. `if_neg` is a stable core lemma.
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        -- Simplify `((k + 1) as nat - 1) as nat` (Tactus renders the
        -- spec fn's `(n - 1) as nat` as `Int.toNat (↑n - 1)`).
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
// Two obligations need help beyond the default closer (`rfl | decide |
// omega | simp_all`): the loop invariant maintain and the postcondition.
// Both involve *nonlinear* arithmetic (a product `i * (i + 1)`), which
// `omega` can't handle. We discharge each with a small `assert(P) by
// { intros; nlinarith }` block at the right spot: two inside the loop
// body (for the two invariants that survive an iteration), one after
// the loop (for the postcondition).

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
            // Bound `result` so overflow on `result + i` is provable
            // without re-deriving the closed-form maximum each time:
            result <= 1001 * 1001,
        decreases n - i
    {
        i = i + 1;
        result = result + i;
        // Re-establish the two nonlinear invariants for the next
        // iteration. omega handles the linear ones automatically.
        assert(2 * result == i * (i + 1)) by { intros; nlinarith };
        assert(result <= 1001 * 1001) by { intros; nlinarith };
    }
    // At exit `i == n`. Combined with the invariant, that gives the
    // postcondition — but the substitution is nonlinear, so omega
    // alone can't close it.
    assert(2 * result == n * (n + 1)) by { intros; nlinarith };
    result
}

fn main() {}

} // verus!
