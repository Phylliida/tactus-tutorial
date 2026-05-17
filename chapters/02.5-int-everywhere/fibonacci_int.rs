// Chapter 2.5: Fibonacci, encoded over `int` instead of `nat`.
//
// Same theorems as Chapter 2 (sum identity, positivity), but every spec
// fn takes and returns `int`. Behavior on negative inputs is "returns 0"
// (the `if n <= 0` guard).
//
// What we gain: no `.toNat` wrappers in proof goals.
// What we pay:
//   1. `decreases (n + 1) as nat` on every recursive spec fn (Verus's
//      `int` decreases needs to project to a nat-valued measure).
//   2. `requires n >= 0` on every induction proof, plus a `| pred k _`
//      vacuous case dismissed by omega.
//   3. We lose type-level non-negativity, so `fib_nonneg` becomes its
//      own lemma — proved via strong induction (self-recursive proof
//      fn), since `fib(n) = fib(n-1) + fib(n-2)` needs *both* sub-
//      values to be non-negative and plain `induction` only gives one.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

// -------- Definitions ----------------------------------------------------

spec fn fib(n: int) -> int
    decreases (n + 1) as nat
{
    if n <= 0 { 0 }
    else if n == 1 { 1 }
    else { fib(n - 1) + fib(n - 2) }
}

spec fn sum_fib(n: int) -> int
    decreases (n + 1) as nat
{
    if n <= 0 { 0 }
    else { fib(n - 1) + sum_fib(n - 1) }
}

// -------- fib_nonneg via strong induction --------------------------------
//
// The "two recursive calls" structure of fib means plain induction
// doesn't reach far enough. We use the recursive-proof-fn pattern:
// the proof is itself a function that calls itself on smaller inputs,
// and `decreases (n + 1) as nat` justifies termination.

proof fn fib_nonneg(n: int)
    ensures fib(n) >= 0
    decreases (n + 1) as nat
by {
    if h : n <= 0 then (
        unfold fib
        rw [if_pos h]
    ) else if h1 : n = 1 then (
        unfold fib
        rw [if_neg (by omega : ¬(n ≤ 0))]
        rw [if_pos h1]
        omega
    ) else (
        have ih1 := fib_nonneg (n - 1)
        have ih2 := fib_nonneg (n - 2)
        unfold fib
        rw [if_neg h]
        rw [if_neg h1]
        omega
    )
}

// -------- The sum identity -----------------------------------------------
//
// Identical statement to Chapter 2, but now `n : int` with an explicit
// `requires n >= 0`. The induction has three cases (zero, succ, pred);
// the `pred` case is vacuous and omega dismisses it.
//
// The inductive-step rewrite is over Int directly — no `.toNat` —
// which is the main payoff of this encoding.

proof fn sum_fib_identity(n: int)
    requires n >= 0
    ensures sum_fib(n) + 1 == fib(n + 1)
by {
    induction n with
    | zero => unfold sum_fib; unfold fib; decide
    | succ k ih =>
        unfold sum_fib
        rw [if_neg (by omega : ¬(↑k + 1 ≤ (0 : Int)))]
        rw [show ((↑k + 1 : Int) - 1) = ↑k from by omega]
        conv_rhs => unfold fib
        rw [if_neg (by omega : ¬(↑k + 1 + 1 ≤ (0 : Int)))]
        rw [if_neg (by omega : (↑k + 1 + 1 : Int) ≠ 1)]
        rw [show ((↑k + 1 + 1 : Int) - 1) = ↑k + 1 from by omega]
        rw [show ((↑k + 1 + 1 : Int) - 2) = ↑k from by omega]
        omega
    | pred k _ => omega
}

fn main() {}

} // verus!
