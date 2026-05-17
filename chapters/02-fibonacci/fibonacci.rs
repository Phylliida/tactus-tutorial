// Chapter 2: Fibonacci identities
//
// Define the Fibonacci sequence as a recursive spec fn with two base
// cases, then prove two classical facts about it:
//
//   1. fib(n) >= 1 for n >= 1 — a positivity warm-up.
//   2. F_0 + F_1 + ... + F_n = F_{n+1} - 1.
//      Stated in nat-friendly form as: sum_fib(n) + 1 == fib(n + 1).

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

// -------- Fibonacci ------------------------------------------------------
//
// Two base cases (n == 0, n == 1) and a recursive step that calls
// `fib` twice. `decreases n` lets the kernel verify termination.

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// -------- Concrete value -------------------------------------------------
//
// fib(7) = 13. `repeat (unfold fib; simp)` keeps unfolding the
// definition until every `fib` call reduces to a literal — eight
// unfold steps in this case.

proof fn fib_seven()
    ensures fib(7) == 13
by {
    repeat (unfold fib; simp)
}

// -------- Warm-up: fib is positive on n >= 1 -----------------------------
//
// One-step induction. The succ case splits on whether `k = 0`:
//   - k = 0: the goal reduces to fib(1) = 1 >= 1, handled by `simp`.
//   - k > 0: the induction hypothesis gives `fib k >= 1`, and
//     `fib (k+1) = fib k + fib (k-1)`, so the sum is >= 1.
//
// `omega` closes the second case once `ih : fib k >= 1` is in scope.

proof fn fib_pos(n: nat)
    requires n >= 1
    ensures fib(n) >= 1
    decreases n
by {
    induction n with
    | zero => omega
    | succ k ih =>
        unfold fib
        -- Eliminate `if k + 1 = 0 then 0 else …` (k + 1 ≥ 1 trivially).
        -- `rw [if_neg …]` rather than `simp` here for stability under
        -- future Mathlib upgrades.
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        by_cases h : k = 0
        · subst h
          -- k = 0, so k + 1 = 1, which the second `if` picks up.
          rw [if_pos (by decide : (0 + 1 : Nat) = 1)]
        · rw [if_neg (by omega : (k + 1 : Nat) ≠ 1)]
          rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]
          have hk : k >= 1 := by omega
          have ihk := ih hk
          omega
}

// -------- The sum identity -----------------------------------------------
//
// Define the partial sum F_0 + F_1 + ... + F_{n-1} as a spec fn.

spec fn sum_fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else { fib((n - 1) as nat) + sum_fib((n - 1) as nat) }
}

// Identity: F_0 + F_1 + ... + F_n = F_{n+1} - 1.
//
// Subtracting 1 doesn't play nicely with `nat`, so we restate as
//     sum_fib(n) + 1 == fib(n + 1)
// which is the same fact without the subtraction.
//
// The proof is one-step induction. The inductive step uses the
// Fibonacci recurrence `fib(k+2) = fib(k+1) + fib(k)`. After
// `unfold fib`, Verus's `(n - 1) as nat` cast renders in Lean
// as `(↑(...) - ...).toNat`. `simp` handles most of these
// automatically; one residue remains, and we close it with a
// short `omega` rewrite.

proof fn sum_fib_identity(n: nat)
    ensures sum_fib(n) + 1 == fib(n + 1)
by {
    induction n with
    | zero => unfold sum_fib; unfold fib; decide
    | succ k ih =>
        -- Unfold sum_fib once on the LHS, eliminate the `if k + 1 = 0`
        -- branch, and clean up the `.toNat` arg of the recursive call.
        unfold sum_fib
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]

        -- Unfold fib on the RHS one step. fib(k + 2) falls through the
        -- two `if` base cases (k + 2 ≠ 0 and k + 2 ≠ 1), so we eliminate
        -- both and simplify the two `.toNat` recursive-call args.
        conv_rhs => unfold fib
        rw [if_neg (by omega : (k + 1 + 1 : Nat) ≠ 0)]
        rw [if_neg (by omega : (k + 1 + 1 : Nat) ≠ 1)]
        rw [show ((↑(k + 1 + 1) : Int) - 1).toNat = k + 1 from by omega]
        rw [show ((↑(k + 1 + 1) : Int) - 2).toNat = k from by omega]
        omega
}

fn main() {}

} // verus!
