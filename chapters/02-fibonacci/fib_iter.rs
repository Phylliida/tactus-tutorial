// Chapter 2 (bonus): iterative Fibonacci, verified against the recursive `fib` spec.
//
// This is the natural "exec verified against recursive math spec" headline —
// the same shape as chapter 1's `sum_iter` but with a recurrence-based
// invariant instead of a closed form.
//
// The proof needs three helper lemmas:
//
//   1. `fib_recurrence(n)`: fib(n + 1) = fib(n) + fib(n - 1) for n >= 1.
//      Used in the loop body to relate the new `b` value to the old.
//
//   2. `fib_monotone(k, m)`: k <= m implies fib(k) <= fib(m).
//      Proved by chaining one-step monotonicity via strong induction.
//      Used in the loop's overflow bound: fib(i + 1) <= fib(n) <= fib(10) <= 55.
//
//   3. `fib_10_bound()`: fib(10) <= 55. A concrete-value sanity check
//      that lets `omega` discharge the overflow obligation numerically.
//
// Once the bug fixes for source-name preservation and cross-fn calls land
// (BUG-loop-local-names-alpha-renamed.md and BUG-no-helper-proof-fn-call-
// from-exec.md), the helper-invocation pattern used here works cleanly.

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

proof fn fib_recurrence(n: nat)
    requires n >= 1
    ensures fib(n + 1) == fib(n) + fib((n - 1) as nat)
by {
    conv_lhs => unfold fib_iter.fib
    rw [if_neg (by omega : (n + 1 : Nat) ≠ 0)]
    rw [if_neg (by omega : (n + 1 : Nat) ≠ 1)]
    rw [show ((↑(n + 1) : Int) - 1).toNat = n from by omega]
    rw [show ((↑(n + 1) : Int) - 2).toNat = (↑n - 1 : Int).toNat from by omega]
}

proof fn fib_monotone(k: nat, m: nat)
    requires k <= m
    ensures fib(k) <= fib(m)
    decreases m - k
by {
    if h : k = m then (
        subst h
        omega
    ) else (
        have hge : m >= 1 := by omega
        have ih := fib_iter.fib_monotone k (m - 1)
        have ih_app := ih (by omega)
        have step : fib_iter.fib (m - 1) <= fib_iter.fib m := by
            by_cases h0 : m = 1
            · subst h0; unfold fib_iter.fib; decide
            · have h_rec : fib_iter.fib m = fib_iter.fib (m - 1) + fib_iter.fib ((↑m - 2 : Int).toNat) := by
                  conv_lhs => unfold fib_iter.fib
                  rw [if_neg (by omega : m ≠ 0)]
                  rw [if_neg h0]
                  rw [show ((↑m : Int) - 1).toNat = m - 1 from by omega]
              omega
        omega
    )
}

proof fn fib_10_bound()
    ensures fib(10 as nat) <= 55
by {
    -- One unfold per recursion level down to the base cases, then
    -- `simp` as the closer. (Avoid intermediate `simp` for stability.)
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    unfold fib_iter.fib
    simp
}

#[verifier::tactus_auto]
fn fib_iter(n: u64) -> (r: u64)
    requires n <= 10
    ensures r as nat == fib(n as nat)
{
    if n == 0 {
        assert(fib(0 as nat) == 0) by { intros; unfold fib_iter.fib; decide };
        return 0;
    }
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 1;
    // The init values a := 0, b := 1, i := 1 are goal-position lets; name them
    // with an explicit `intro` (plain `intros` leaves them inaccessible) — the
    // leading `_` is the ¬(n = 0) hyp from the early return.
    assert(a as nat == fib((i - 1) as nat)) by {
        intro _ a b i
        have h0 : (i - 1 : Int).toNat = 0 := by omega
        rw [h0]; unfold fib_iter.fib; decide
    };
    assert(b as nat == fib(i as nat)) by {
        intro _ a b i _ _
        have h1 : i.toNat = 1 := by omega
        rw [h1]; unfold fib_iter.fib; decide
    };
    while i < n
        invariant
            1 <= i,
            i <= n,
            n <= 10,
            a as nat == fib((i - 1) as nat),
            b as nat == fib(i as nat),
            a <= 55,
            b <= 55,
        decreases n - i
    {
        assert(fib((i + 1) as nat) == fib(i as nat) + fib((i - 1) as nat)) by {
            intros
            have h := fib_iter.fib_recurrence i.toNat
            have hge : i.toNat >= 1 := by omega
            have h2 := h hge
            have e1 : (i.toNat + 1 : Nat) = (i + 1 : Int).toNat := by omega
            have e2 : (↑i.toNat - 1 : Int).toNat = (i - 1 : Int).toNat := by omega
            rw [e1, e2] at h2
            exact h2
        };
        assert(fib((i + 1) as nat) <= 55) by {
            intros
            have mono := fib_iter.fib_monotone ((i + 1 : Int).toNat) 10
            have mono_app := mono (by omega)
            have b10 : fib_iter.fib (10 : Nat) <= 55 := fib_iter.fib_10_bound 0
            omega
        };
        let tmp = a + b;
        a = b;
        b = tmp;
        i = i + 1;
    }
    assert(b as nat == fib(n as nat)) by {
        intros
        have heq : i = n := by omega
        have heq_nat : i.toNat = n.toNat := by omega
        subst heq
        omega
    };
    b
}

fn main() {}

} // verus!
