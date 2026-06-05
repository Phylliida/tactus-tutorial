// Chapter 6: iterative Euclidean gcd, verified against the recursive `gcd` spec.
//
// The cleanest iterative-vs-recursive chapter in the tutorial, because the
// recursive spec
//     gcd(a, b) = if b == 0 { a } else { gcd(b, a % b) }
// *is* the loop step. Euclid's algorithm just runs that one rewrite until the
// second argument hits zero. So the loop invariant is a one-liner —
//     gcd(x, y) == gcd(a, b)
// "the gcd of the current pair equals the gcd of the original pair" — and the
// maintain step is a *single unfold* of the spec. No crux lemma (unlike
// chapter 5's `pow_square`); no monotonicity / bound lemmas (unlike chapter 4).
//
// There is also no overflow story at all: x and y only ever shrink
// (`x % y < y`), so nothing can exceed the inputs.
//
// What this chapter introduces is modular arithmetic in the *termination*
// argument. Both the spec's `decreases b` (needs `a % b < b`) and the loop's
// `decreases y` (needs `x % y < y`) rest on "the remainder is smaller than the
// divisor." Crucially `omega` CANNOT prove this — it only reasons about `%` by
// a *literal* divisor, and here the divisor is a variable. So:
//   - spec side (Nat): `Nat.mod_lt` discharges termination (handled by Tactus's
//     spec-fn `decreasing_by`).
//   - exec side (Int, since u64 renders as Int): `Int.emod_lt_of_pos` is invoked
//     in an explicit assert that feeds the loop's `decreases y` check.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith

spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}

// Euclid's algorithm. The invariant gcd(x, y) == gcd(a, b) holds at entry
// (x = a, y = b) and is maintained by one unfold of the spec each step. At exit
// y == 0, so gcd(x, 0) == x collapses the invariant to x == gcd(a, b) — the
// postcondition.
//
// The closer's `(intros; omega)` branch handles the loop's `decreases y`
// obligation, which Tactus renders with a `let _tactus_d_old := y; …` binding
// for the old measure: `intros` introduces that let so `omega` can chain the
// asserted `x % y < y` (the new y) against it.
#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; omega)")]
fn gcd_iter(a: u64, b: u64) -> (g: u64)
    ensures g as nat == gcd(a as nat, b as nat)
{
    let mut x: u64 = a;
    let mut y: u64 = b;
    while y > 0
        invariant
            gcd(x as nat, y as nat) == gcd(a as nat, b as nat),
        decreases y
    {
        // (1) Termination of the loop. The new y is `x % y`, so `decreases y`
        // needs `x % y < y`. omega can't (variable divisor), so we hand it
        // `Int.emod_lt_of_pos` (u64 is rendered as Int); the side goal `0 < y`
        // comes from the loop condition. With this fact in scope the decrease
        // check closes.
        assert(x % y < y) by {
            intros
            apply Int.emod_lt_of_pos <;> omega
        };
        // (2) Maintain. After `x = y; y = x % y` we need
        //     gcd(y_old, x_old % y_old) == gcd(a, b).
        // The spec unfolds (y != 0) to gcd(x, y) = gcd(y, x % y); the invariant
        // gives gcd(x, y) = gcd(a, b); chaining the two yields the goal. The one
        // piece of cast plumbing: `(x % y) as nat` renders as Int-emod-then-toNat,
        // while the spec's body uses Nat mod, so `Int.toNat_emod` bridges them.
        assert(gcd(y as nat, (x % y) as nat) == gcd(a as nat, b as nat)) by {
            intros
            have hmod : ((x % y : Int)).toNat = x.toNat % y.toNat :=
                Int.toNat_emod (by omega) (by omega)
            have hunf : gcd x.toNat y.toNat = gcd y.toNat (x.toNat % y.toNat) := by
                conv_lhs => unfold gcd
                rw [if_neg (by omega : y.toNat ≠ 0)]
            rw [hmod, ← hunf]
            assumption
        };
        let r = x % y;
        x = y;
        y = r;
    }
    // (3) Exit. y == 0, so gcd(x, 0) == x (the spec's base case), and the
    // invariant gcd(x, 0) == gcd(a, b) gives x == gcd(a, b).
    //
    // The postcondition `x as nat == gcd(a, b)` renders in ℤ as
    // `x = ↑(gcd a.toNat b.toNat)` (x stays Int; the nat-valued gcd is lifted).
    // So we establish the ℕ equation `x.toNat = gcd a.toNat b.toNat` by walking
    // the invariant through `y == 0` and the base case, then let `omega` bridge
    // the lift (it knows `x ≥ 0 ==> ↑x.toNat = x`).
    assert(x as nat == gcd(a as nat, b as nat)) by {
        intros
        have hy0 : y.toNat = 0 := by omega
        have hbase : gcd x.toNat (0 : Nat) = x.toNat := by unfold gcd; simp
        have hinv : gcd x.toNat y.toNat = gcd a.toNat b.toNat := by assumption
        rw [hy0] at hinv
        rw [hbase] at hinv      // hinv : x.toNat = gcd a.toNat b.toNat
        omega
    };
    x
}

fn main() {}

} // verus!
