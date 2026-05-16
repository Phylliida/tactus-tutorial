// Chapter 3: Strong induction
//
// Plain induction (Chapter 2) lets you assume `P k` and prove `P (k + 1)`.
// Some proofs need MORE — the inductive step asks about smaller values
// that plain induction can't reach. Fibonacci is the canonical case:
// fib(n) = fib(n - 1) + fib(n - 2), so a proof about fib(n) often
// needs hypotheses at BOTH n - 1 and n - 2.
//
// We prove `fib(n) <= 2^n` — a loose bound that's easy to state and
// genuinely needs strong induction.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

// fib(n) <= 2^n.
//
// Two base cases (n = 0 and n = 1), then a recursive case that calls
// `fib_le_pow2` at BOTH `n - 1` and `n - 2`. The `decreases n` clause
// justifies termination — both recursive calls have a smaller measure.

proof fn fib_le_pow2(n: nat)
    ensures fib(n) <= pow2(n)
    decreases n
by {
    if h0 : n = 0 then (
        subst h0; unfold fib; unfold pow2; simp
    ) else if h1 : n = 1 then (
        subst h1; unfold fib; repeat (unfold pow2; simp)
    ) else (
        -- Strong induction: invoke the proof recursively at both
        -- `n - 1` and `n - 2`. Lean threads the `decreases` measure
        -- to verify these calls are well-founded.
        have ih1 := fib_le_pow2 (n - 1)
        have ih2 := fib_le_pow2 (n - 2)
        have hf0 : ¬(n = 0) := by omega
        have hf1 : ¬(n = 1) := by omega
        have hn1z : ¬(n - 1 = 0) := by omega

        -- Helper 1: pow2(n) = pow2(n-1) + pow2(n-1).
        -- Comes from unfolding pow2 once: pow2(n) = 2 * pow2(n-1).
        have pow_unfold : pow2 n = pow2 (n - 1) + pow2 (n - 1) := by
            conv_lhs => unfold pow2
            simp [hf0]
            omega

        -- Helper 2: pow2 is monotone. pow2(n-2) <= pow2(n-1) because
        -- pow2(n-1) = 2 * pow2(n-2).
        have pow_mono : pow2 (n - 2) <= pow2 (n - 1) := by
            conv_rhs => unfold pow2
            simp [hn1z]
            have h_sub : n - 1 - 1 = n - 2 := by omega
            rw [h_sub]
            omega

        -- Unfold fib on the LHS to expose fib(n) = fib(n-1) + fib(n-2).
        conv_lhs => unfold fib
        simp [hf0, hf1]
        rw [show ((↑n : Int) - 2).toNat = n - 2 from by omega]

        -- Now goal: fib(n-1) + fib(n-2) <= pow2(n).
        -- omega combines ih1, ih2, pow_unfold, pow_mono to finish.
        omega
    )
}

fn main() {}

} // verus!
