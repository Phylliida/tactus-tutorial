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
        subst h0; unfold fib; unfold pow2; decide
    ) else if h1 : n = 1 then (
        subst h1
        unfold fib
        rw [if_neg (by decide : (1 : Nat) ≠ 0)]
        rw [if_pos (by decide : (1 : Nat) = 1)]
        unfold pow2
        rw [if_neg (by decide : (1 : Nat) ≠ 0)]
        rw [show ((↑(1 : Nat) : Int) - 1).toNat = 0 from by omega]
        unfold pow2
        decide
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
        --
        -- We use `rw [if_neg …]` to eliminate the `if n = 0` branch
        -- rather than a bare `simp`. `simp`'s behavior depends on
        -- Mathlib's evolving `@[simp]` set — pinned lemmas like
        -- `if_neg` are stable. See the README's "simp robustness" note.
        have pow_unfold : pow2 n = pow2 (n - 1) + pow2 (n - 1) := by
            conv_lhs => unfold pow2
            rw [if_neg hf0]
            rw [show ((↑n : Int) - 1).toNat = n - 1 from by omega]
            omega

        -- Helper 2: pow2 is monotone. pow2(n-2) <= pow2(n-1) because
        -- pow2(n-1) = 2 * pow2(n-2).
        have pow_mono : pow2 (n - 2) <= pow2 (n - 1) := by
            conv_rhs => unfold pow2
            rw [if_neg hn1z]
            rw [show ((↑(n - 1) : Int) - 1).toNat = n - 2 from by omega]
            omega

        -- Unfold fib on the LHS to expose fib(n) = fib(n-1) + fib(n-2).
        conv_lhs => unfold fib
        rw [if_neg hf0]
        rw [if_neg hf1]
        rw [show ((↑n : Int) - 1).toNat = n - 1 from by omega]
        rw [show ((↑n : Int) - 2).toNat = n - 2 from by omega]

        -- Now goal: fib(n-1) + fib(n-2) <= pow2(n).
        -- omega combines ih1, ih2, pow_unfold, pow_mono to finish.
        omega
    )
}

// ============================================================================
// The Fibonacci addition formula
// ============================================================================
//
// The canonical strong-induction result for Fibonacci:
//
//     F_{m+n+1} = F_m · F_n + F_{m+1} · F_{n+1}
//
// Same strong-induction *shape* as fib_le_pow2 — two base cases
// (m = 0, m = 1) and a recursive case that uses the IH at both m - 1
// and m - 2 — but the algebra in the recursive case is heavier: we
// combine two IH instances with the Fibonacci recurrence applied at
// three different positions.
//
// Why it matters: substituting m = n into the addition formula gives
// F_{2n+1} = F_n² + F_{n+1}². Combined with F_{2n} = F_n · (2·F_{n+1} − F_n),
// this is the basis of *fast-doubling Fibonacci* — an O(log n) algorithm
// for computing F_n.

proof fn fib_addition(m: nat, n: nat)
    ensures fib(m + n + 1) == fib(m) * fib(n) + fib(m + 1) * fib(n + 1)
    decreases m
by {
    if h0 : m = 0 then (
        -- F_{n+1} = F_0 · F_n + F_1 · F_{n+1} = 0 + 1·F_{n+1}.
        -- Bare `simp` as a closer is fine (simp robustness only bites
        -- when downstream tactics depend on a specific intermediate form).
        subst h0; unfold fib; simp
    ) else if h1 : m = 1 then (
        -- F_{n+2} = F_1 · F_n + F_2 · F_{n+1} = F_n + F_{n+1}.
        -- Compute F_1, F_2 explicitly, then unfold F_{n+2}.
        subst h1
        have f1 : fib 1 = 1 := by unfold fib; simp
        have f2 : fib 2 = 1 := by unfold fib; unfold fib; unfold fib; simp
        have step : fib (n + 2) = fib (n + 1) + fib n := by
            conv_lhs => unfold fib
            rw [if_neg (by omega : (n + 2 : Nat) ≠ 0)]
            rw [if_neg (by omega : (n + 2 : Nat) ≠ 1)]
            rw [show ((↑(n + 2) : Int) - 1).toNat = n + 1 from by omega]
            rw [show ((↑(n + 2) : Int) - 2).toNat = n from by omega]
        have h_lhs : 1 + n + 1 = n + 2 := by omega
        rw [h_lhs, f1, f2, step]
        linarith
    ) else (
        -- Recursive case (m >= 2): combine the IH at m - 1 and m - 2
        -- with the Fibonacci recurrence applied at three positions.
        have hm2 : m >= 2 := by omega
        have h_m0 : ¬(m = 0) := by omega
        have h_m1 : ¬(m = 1) := by omega

        -- Two recursive calls — the strong-induction step.
        have ih1 := fib_addition (m - 1) n
        have ih2 := fib_addition (m - 2) n

        -- Simplify subscripts in the IHs so they refer to m and n cleanly.
        --   ih1 : fib (m + n)     = fib (m - 1) · fib n + fib m       · fib (n + 1)
        --   ih2 : fib (m + n - 1) = fib (m - 2) · fib n + fib (m - 1) · fib (n + 1)
        have e1a : (m - 1) + n + 1 = m + n := by omega
        have e1b : (m - 1) + 1 = m := by omega
        rw [e1a, e1b] at ih1

        have e2a : (m - 2) + n + 1 = m + n - 1 := by omega
        have e2b : (m - 2) + 1 = m - 1 := by omega
        rw [e2a, e2b] at ih2

        -- Three instances of the Fibonacci recurrence:
        --   F_m       = F_{m-1} + F_{m-2}
        --   F_{m+1}   = F_m + F_{m-1}
        --   F_{m+n+1} = F_{m+n} + F_{m+n-1}
        -- Each is one unfold of fib followed by `rw [if_neg …]` to drop
        -- the two base cases and `rw [show … toNat … from by omega]` to
        -- clean up the recursive-call args.
        have step_m : fib m = fib (m - 1) + fib (m - 2) := by
            conv_lhs => unfold fib
            rw [if_neg h_m0]
            rw [if_neg h_m1]
            rw [show ((↑m : Int) - 1).toNat = m - 1 from by omega]
            rw [show ((↑m : Int) - 2).toNat = m - 2 from by omega]

        have step_m1 : fib (m + 1) = fib m + fib (m - 1) := by
            conv_lhs => unfold fib
            rw [if_neg (by omega : (m + 1 : Nat) ≠ 0)]
            rw [if_neg (by omega : (m + 1 : Nat) ≠ 1)]
            rw [show ((↑(m + 1) : Int) - 1).toNat = m from by omega]
            rw [show ((↑(m + 1) : Int) - 2).toNat = m - 1 from by omega]

        have step_sum : fib (m + n + 1) = fib (m + n) + fib (m + n - 1) := by
            conv_lhs => unfold fib
            rw [if_neg (by omega : (m + n + 1 : Nat) ≠ 0)]
            rw [if_neg (by omega : (m + n + 1 : Nat) ≠ 1)]
            rw [show ((↑(m + n + 1) : Int) - 1).toNat = m + n from by omega]
            rw [show ((↑(m + n + 1) : Int) - 2).toNat = m + n - 1 from by omega]

        -- Combine:
        --   F_{m+n+1} = F_{m+n} + F_{m+n-1}
        --             = (F_{m-1} F_n + F_m F_{n+1}) + (F_{m-2} F_n + F_{m-1} F_{n+1})
        --             = (F_{m-1} + F_{m-2}) F_n + (F_m + F_{m-1}) F_{n+1}
        --             = F_m F_n + F_{m+1} F_{n+1}
        -- The arithmetic involves products (so omega isn't enough);
        -- nlinarith handles polynomial identities given the facts.
        nlinarith [step_sum, ih1, ih2, step_m, step_m1]
    )
}

fn main() {}

} // verus!
