// Chapter 5: exponentiation by squaring, verified against recursive `pow`.
//
// The capstone. We verify a *fast* (O(log e)) Rust implementation against
// the *slow* (O(e)) recursive mathematical definition. Same value, but the
// algorithm is exponentially faster — and the proof guarantees they agree
// for every input in range.
//
// Three self-contained helper lemmas:
//   - pow_pos:     base >= 1  ==>  pow(base, e) >= 1.
//   - pow_ge_base: base >= 1, e >= 1  ==>  pow(base, e) >= base.
//   - pow_square:  pow(base*base, k) == pow(base, 2*k).   The crux: it lets
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
        have rec_app : pow base e = base * pow base ((↑e - 1 : Int).toNat) := by
            conv_lhs => unfold pow
            rw [if_neg (by omega : e ≠ 0)]
        have ee : ((↑e - 1 : Int).toNat) = e - 1 := by omega
        rw [ee] at rec_app
        have h_prod : 1 * 1 <= base * pow base (e - 1) := by
            apply Nat.mul_le_mul <;> omega
        omega
    )
}

// pow(base, e) >= base when base >= 1, e >= 1. Self-recursive.
proof fn pow_ge_base(base: nat, e: nat)
    requires base >= 1, e >= 1
    ensures pow(base, e) >= base
    decreases e
by {
    have hrec : pow base e = base * pow base (e - 1) := by
        conv_lhs => unfold pow
        rw [if_neg (by omega : e ≠ 0)]
        rw [show ((e : Int) - 1).toNat = e - 1 from by omega]
    if h : e = 1 then (
        rw [hrec]
        rw [show (e - 1) = 0 from by omega]
        unfold pow
        simp
    ) else (
        have ih := pow_ge_base base (e - 1) (by omega) (by omega)
        rw [hrec]
        nlinarith [ih]
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

// Exponentiation by squaring. result accumulates the answer; b holds the
// running square base^(2^k); e is the remaining exponent, halved each step.
//
// Invariant: result * pow(b, e) == pow(base, exp). At exit e == 0, so
// pow(b, 0) == 1 and result == pow(base, exp).
//
// Overflow: in the loop body (e >= 1) we have b <= pow(b, e) <= pow(base,
// exp) <= 2^31, so b*b <= 2^62 and result*b <= 2^31 both fit in u64. The
// precondition `pow(base, exp) <= 2^31` is what a fixed-width implementation
// needs; a bignum version wouldn't.
//
// The closer handles the linear/nonlinear obligations the default ladder
// can't (the `1 <= b` / `1 <= result` maintains, overflow checks); the
// per-step asserts feed it the recurrence facts about `pow`.
#[verifier::tactus_auto]
fn pow_iter(base: u64, exp: u64) -> (r: u64)
    requires
        base >= 1,
        pow(base as nat, exp as nat) <= 0x8000_0000,
    ensures r as nat == pow(base as nat, exp as nat)
{
    let mut result: u64 = 1;
    let mut b: u64 = base;
    let mut e: u64 = exp;
    while e > 0
        invariant
            1 <= b,
            1 <= result,
            (result as nat) * pow(b as nat, e as nat) == pow(base as nat, exp as nat),
            pow(base as nat, exp as nat) <= 0x8000_0000,
        decreases e
    {
        // (A) b <= pow(b,e) <= result*pow(b,e) = pow(base,exp). Prove the
        // nat statement (where the invariant lives), then omega lifts it.
        assert(b as nat <= pow(base as nat, exp as nat)) by {
            intros
            have hge := pow_ge_base b.toNat e.toNat (by omega) (by omega)
            have hr1 : (1 : Nat) <= result.toNat := by omega
            have hN : b.toNat <= pow base.toNat exp.toNat := by nlinarith [hge, hr1]
            omega
        };
        // (B) b*b fits in u64: b <= 2^31 (from A + the invariant bound), so b*b <= 2^62.
        // A concrete literal bound, so the b*b overflow check needs no ℕ/ℤ bridging.
        assert(b * b <= 0x4000_0000_0000_0000) by {
            intros
            have hb31 : b <= 0x8000_0000 := by omega
            nlinarith [hb31]
        };
        if e % 2 == 1 {
            // Odd: pow(b,e) = b * pow(b,e-1) = b * pow(b*b, e/2)  (since 2*(e/2) = e-1).
            // So (result*b) * pow(b*b, e/2) = result * pow(b,e) = pow(base,exp).
            assert((result * b) as nat * pow((b * b) as nat, (e / 2) as nat) == pow(base as nat, exp as nat)) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by rw [Int.toNat_mul] <;> omega
                have hrb : ((result * b : Int)).toNat = result.toNat * b.toNat := by rw [Int.toNat_mul] <;> omega
                have hsq := pow_square b.toNat (e / 2).toNat
                have he : 2 * (e / 2).toNat = e.toNat - 1 := by omega
                rw [he] at hsq
                have hrec : pow b.toNat e.toNat = b.toNat * pow b.toNat (e.toNat - 1) := by
                    conv_lhs => unfold pow
                    rw [if_neg (by omega : e.toNat ≠ 0)]
                    rw [show ((e.toNat : Int) - 1).toNat = e.toNat - 1 from by omega]
                rw [hbb, hrb, hsq, mul_assoc, ← hrec]
                linarith
            };
            // result*b <= pow(base,exp) <= 2^31 (from the maintain eq + pow >= 1).
            // A concrete literal bound, so the result*b overflow check is clean.
            assert(result * b <= 0x8000_0000) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by rw [Int.toNat_mul] <;> omega
                have hb1 : (1 : Nat) <= b.toNat := by omega
                have hpos := pow_pos ((b * b : Int)).toNat (e / 2).toNat (by rw [hbb]; nlinarith [hb1])
                have hN : (result * b : Int).toNat <= 0x8000_0000 := by nlinarith [hpos]
                have hnn : (0 : Int) <= result * b := by nlinarith
                omega
            };
            // result*b >= 0 for the overflow check's lower bound (the variable
            // range bounds are conjunctions, so nlinarith can't reach 0<=result, 0<=b).
            assert(0 <= result * b) by {
                intros
                have hr : (0 : Int) <= result := by omega
                have hb : (0 : Int) <= b := by omega
                nlinarith [hr, hb]
            };
            // Maintain `1 <= result`: after `result = result * b`, the product
            // is >= 1 from `1 <= result` and `1 <= b`. Previously absorbed by
            // the whole-fn closer's `(intros; nlinarith)`; now a local
            // fixed-menu `by(nonlinear_arith)` at the exact site.
            assert(1 <= result * b) by(nonlinear_arith)
                requires 1 <= result, 1 <= b;
            result = result * b;
        } else {
            // Even: pow(b,e) = pow(b*b, e/2)  (since 2*(e/2) = e).
            assert((result as nat) * pow((b * b) as nat, (e / 2) as nat) == pow(base as nat, exp as nat)) by {
                intros
                have hbb : ((b * b : Int)).toNat = b.toNat * b.toNat := by rw [Int.toNat_mul] <;> omega
                have hsq := pow_square b.toNat (e / 2).toNat
                have he : 2 * (e / 2).toNat = e.toNat := by omega
                rw [he] at hsq
                rw [hbb, hsq]
                linarith
            };
        }
        // b*b >= 0 for the overflow check's lower bound.
        assert(0 <= b * b) by {
            intros
            have hb : (0 : Int) <= b := by omega
            nlinarith [hb]
        };
        // Maintain `1 <= b`: after `b = b * b`, `b*b >= 1` from `1 <= b`.
        assert(1 <= b * b) by(nonlinear_arith) requires 1 <= b;
        b = b * b;
        e = e / 2;
    }
    // At exit e == 0, so pow(b, 0) == 1 and result == pow(base, exp).
    assert(result as nat == pow(base as nat, exp as nat)) by {
        intros
        have he0 : e.toNat = 0 := by omega
        have h1 : pow b.toNat e.toNat = 1 := by rw [he0]; unfold pow; simp
        have hN : result.toNat = pow base.toNat exp.toNat := by nlinarith [h1]
        omega
    };
    result
}

fn main() {}

} // verus!
