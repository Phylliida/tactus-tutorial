// Chapter 4: iterative factorial, verified against the recursive `fact` spec.
//
// Same shape as chapter 2's `fib_iter`, but the recurrence is
// multiplicative (`fact(n + 1) = (n + 1) * fact(n)`) rather than
// additive. That difference matters in three places:
//
//   1. Monotonicity. `fact_monotone` chains one-step growth: from
//      `fact(m) = m * fact(m-1)` and `m >= 1` we get
//      `m * fact(m-1) >= 1 * fact(m-1) = fact(m-1)` (Nat.mul_le_mul_right),
//      and the IH carries `fact(k) <= fact(m-1)`.
//
//   2. Overflow. `result * (i + 1)` for u64 needs a bound; we use
//      `fact_monotone` and a concrete `fact(10) <= 3628800` to discharge.
//
//   3. Maintain step. After `result = result * (i + 1)`, we need
//      `result == fact(i + 1)`. The chain
//          result * (i + 1) = (i + 1) * fact(i) = fact(i + 1)
//      uses commutativity of multiplication plus the recurrence — not
//      something `omega` handles. We pre-prove it as an inline
//      `assert(result * (i + 1) == fact((i + 1) as nat)) by { nlinarith }`
//      so the maintain step closes with `omega` after the assignment.
//
// Helpers: `fact_monotone` and `fact_10_bound` feed the overflow bound.
// `fact_pos` (`n! >= 1`) is a standalone positivity fact — the proofs
// above don't actually need it (monotonicity goes through `m >= 1`), but
// it's a clean example of the self-recursive proof shape and a fact worth
// having on the shelf.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

proof fn fact_pos(n: nat)
    ensures fact(n) >= 1
    decreases n
by {
    if h : n = 0 then (
        subst h; unfold fact; decide
    ) else (
        have ih := fact_pos (n - 1)
        have rec_app : fact n = n * fact ((↑n : Int) - 1).toNat := by
            conv_lhs => unfold fact
            rw [if_neg (by omega : n ≠ 0)]
        have e : ((↑n : Int) - 1).toNat = n - 1 := by omega
        rw [e] at rec_app
        have h_prod : 1 * 1 <= n * fact (n - 1) := by
            apply Nat.mul_le_mul <;> omega
        omega
    )
}

proof fn fact_monotone(k: nat, m: nat)
    requires k <= m
    ensures fact(k) <= fact(m)
    decreases m - k
by {
    if h : k = m then (
        subst h; omega
    ) else (
        have ih := fact_monotone k (m - 1)
        have ih_app := ih (by omega)
        have step : fact (m - 1) <= fact m := by
            have rec_app : fact m = m * fact ((↑m : Int) - 1).toNat := by
                conv_lhs => unfold fact
                rw [if_neg (by omega : m ≠ 0)]
            have e : ((↑m : Int) - 1).toNat = m - 1 := by omega
            rw [e] at rec_app
            have h_step : 1 * fact (m - 1) <= m * fact (m - 1) := by
                apply Nat.mul_le_mul_right; omega
            omega
        omega
    )
}

proof fn fact_10_bound()
    ensures fact(10 as nat) <= 3628800
by {
    repeat unfold fact
    decide
}

#[verifier::tactus_auto]
fn factorial(n: u64) -> (r: u64)
    requires n <= 10
    ensures r as nat == fact(n as nat)
{
    let mut result: u64 = 1;
    let mut i: u64 = 0;
    assert(result as nat == fact(i as nat)) by {
        intros
        have h : i.toNat = 0 := by omega
        rw [h]; unfold fact; decide
    };
    while i < n
        invariant
            i <= n,
            n <= 10,
            result as nat == fact(i as nat),
            result <= 3628800,
        decreases n - i
    {
        // (1) recurrence: fact(i+1) = (i+1) * fact(i).
        //   `rec_app` unfolds fact once, dropping the `== 0` base case.
        //   `e` rewrites the toNat-wrapped recursive index to `i.toNat`.
        //   The goal is stated over Int (the loop vars are u64 → Int), but
        //   `rec_app` is a Nat equation, so `zify` lifts it to Int and `e2`
        //   normalizes the `(i+1).toNat` cast before `linarith` matches.
        assert(fact((i + 1) as nat) == (i + 1) * fact(i as nat)) by {
            intros
            have rec_app : fact ((i + 1 : Int).toNat) = (i + 1 : Int).toNat * fact ((↑((i + 1 : Int).toNat) : Int) - 1).toNat := by
                conv_lhs => unfold fact
                rw [if_neg (by omega : ((i + 1 : Int).toNat : Nat) ≠ 0)]
            have e : ((↑((i + 1 : Int).toNat) : Int) - 1).toNat = i.toNat := by omega
            have e2 : ((i + 1 : Int).toNat : Int) = i + 1 := by omega
            rw [e] at rec_app
            zify at rec_app   -- lift the Nat equation rec_app up to Int
            rw [e2] at rec_app
            linarith [rec_app]
        };
        // (2) bound: result * (i + 1) <= 3628800.
        //   The invariant gives `result.toNat = fact i.toNat` (ℕ) and the goal
        //   is in ℤ, so we bridge the casts with omega before nlinarith: `hri`
        //   lifts the invariant to `result = ↑(fact i.toNat)`, and `hb` lifts
        //   the ℕ bound chain (mono_app, b10) up to ℤ. nlinarith then combines
        //   them with the recurrence (assert (1), in context).
        assert(result * (i + 1) <= 3628800) by {
            intros
            have mono := fact_monotone ((i + 1 : Int).toNat) 10
            have mono_app := mono (by omega)
            have b10 : fact (10 : Nat) <= 3628800 := fact_10_bound 0
            have hri : result = (fact i.toNat : Int) := by omega
            have hb : (fact ((i + 1 : Int).toNat) : Int) <= 3628800 := by omega
            nlinarith [hri, hb]
        };
        // (3) result * (i + 1) = fact(i+1) -- needed for maintain.
        //   Same ℤ/ℕ bridge: with `result = ↑(fact i.toNat)` and the recurrence
        //   (assert (1)), nlinarith closes result*(i+1) = ↑(fact (i+1).toNat).
        assert(result * (i + 1) == fact((i + 1) as nat)) by {
            intros
            have hri : result = (fact i.toNat : Int) := by omega
            nlinarith [hri]
        };
        result = result * (i + 1);
        i = i + 1;
    }
    assert(result as nat == fact(n as nat)) by {
        intros
        have heq : i = n := by omega
        subst heq
        omega
    };
    result
}

fn main() {}

} // verus!
