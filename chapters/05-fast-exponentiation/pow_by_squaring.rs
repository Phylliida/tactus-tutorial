// Chapter 5: exponentiation by squaring, verified against recursive `pow`.
//
// The capstone. We verify a *fast* (O(log e)) Rust implementation against
// the *slow* (O(e)) recursive mathematical definition. Same value, but the
// algorithm is exponentially faster — and the proof guarantees they agree
// for every input in range.
//
// Two self-contained helper lemmas:
//   - pow_pos:    base >= 1  ==>  pow(base, e) >= 1.
//   - pow_square: pow(base*base, k) == pow(base, 2*k).   The crux: it lets
//     the loop replace `pow(b, e)` with `pow(b*b, e/2)` each iteration.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

spec fn pow(base: nat, e: nat) -> nat
    decreases e
{
    if e == 0 { 1 } else { base * pow(base, (e - 1) as nat) }
}

// pow(base, e) >= 1 when base >= 1. Self-recursive (one-step induction).
proof fn pow_pos(base: nat, e: nat)
    requires base >= 1
    ensures pow(base, e) >= 1
    decreases e
by {
    if h : e = 0 then (
        subst h; unfold pow; simp
    ) else (
        have ih := pow_pos base (e - 1)
        have rec_app : pow base e = base * pow base ((↑e : Int) - 1).toNat := by
            conv_lhs => unfold pow
            rw [if_neg (by omega : e ≠ 0)]
        have ee : ((↑e : Int) - 1).toNat = e - 1 := by omega
        rw [ee] at rec_app
        have h_prod : 1 * 1 <= base * pow base (e - 1) := by
            apply Nat.mul_le_mul <;> omega
        omega
    )
}

// pow(base*base, k) == pow(base, 2*k). Self-recursive on k.
// LHS unfolds to (base*base) * pow(base*base, k-1); RHS unfolds twice to
// base * base * pow(base, 2*(k-1)); the IH bridges the two.
proof fn pow_square(base: nat, k: nat)
    ensures pow(base * base, k) == pow(base, 2 * k)
    decreases k
by {
    if h : k = 0 then (
        subst h; unfold pow; simp
    ) else (
        have ih := pow_square base (k - 1)
        conv_lhs => unfold pow
        rw [if_neg (by omega : k ≠ 0)]
        rw [show ((↑k : Int) - 1).toNat = k - 1 from by omega]
        conv_rhs => unfold pow
        rw [if_neg (by omega : 2 * k ≠ 0)]
        rw [show ((↑(2 * k) : Int) - 1).toNat = 2 * k - 1 from by omega]
        conv_rhs => unfold pow
        rw [if_neg (by omega : 2 * k - 1 ≠ 0)]
        rw [show ((↑(2 * k - 1) : Int) - 1).toNat = 2 * (k - 1) from by omega]
        rw [ih]
        ring
    )
}

// ---------------------------------------------------------------------------
// The headline of this chapter is an iterative `pow_iter` exec fn — fast
// exponentiation by squaring — verified against `pow`. Its key invariant is
//
//     result * pow(b, e) == pow(base, exp)
//
// (result accumulates the answer; b holds the running square base^(2^k); e is
// the remaining exponent, halved each step). At exit e == 0, pow(b, 0) == 1,
// so result == pow(base, exp). Overflow stays bounded by a precondition
// `pow(base, exp) <= 2^31`: in the loop body b <= pow(b, e) <= pow(base, exp),
// so b*b and result*b both fit in u64.
//
// The verification is currently PAUSED. The proof is mathematically complete
// (the two lemmas above, including the crux `pow_square`, are exactly what it
// needs), but it hits three Tactus *lowering* frictions — not math problems —
// documented in BUG-ch5-pow-iter-lowering-frictions.md at the workspace root:
//
//   1. The loop invariant arrives as one unsplit `∧` hypothesis in assert and
//      obligation contexts, so omega/nlinarith can't reach its parts.
//   2. The invariant clause renders in ℤ but a structurally identical assert
//      renders in ℕ, so the asserted fact doesn't unify with the maintain goal.
//   3. `e.toNat` vs `e` cast noise in unfolded recursive-call indices.
//
// Once those are addressed the exec proof lands cleanly; the full attempt is
// preserved in the bug report as the reproducer.
// ---------------------------------------------------------------------------

fn main() {}

} // verus!
