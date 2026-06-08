use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else if n == 1 { 1 } else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// A 2x2 matrix [[a, b], [c, d]] over nat.
struct Mat2 { a: nat, b: nat, c: nat, d: nat }

// Matrix product. [[a,b],[c,d]] · [[e,f],[g,h]] = [[ae+bg, af+bh], [ce+dg, cf+dh]].
spec fn mat_mul(m: Mat2, n: Mat2) -> Mat2 {
    Mat2 {
        a: m.a * n.a + m.b * n.c,
        b: m.a * n.b + m.b * n.d,
        c: m.c * n.a + m.d * n.c,
        d: m.c * n.b + m.d * n.d,
    }
}

// M^e, the *slow* recursive definition (mirrors ch5's `pow`): M^0 = I (the
// identity [[1,0],[0,1]]), M^e = M · M^(e-1).
spec fn mat_pow(m: Mat2, e: nat) -> Mat2
    decreases e
{
    if e == 0 { Mat2 { a: 1, b: 0, c: 0, d: 1 } } else { mat_mul(m, mat_pow(m, (e - 1) as nat)) }
}

// ── The Fibonacci identity ──────────────────────────────────────────────────
// With the Fibonacci Q-matrix Q = [[1,1],[1,0]]:
//   Q^(n+1) = [[F(n+2), F(n+1)], [F(n+1), F(n)]]
// (indices shifted by +1 so every entry is a genuine nat — no F(-1)).
// Induction on n: Q^(n+1) = Q · Q^n, and Q · [[F(n+1),F(n)],[F(n),F(n-1)]] folds
// to [[F(n+2),F(n+1)],[F(n+1),F(n)]] via two Fibonacci recurrences.
//
// Q and I are written as literals (not nullary spec fns): a 0-arg spec fn
// renders inconsistently across Tactus's per-fn and aggregate Lean files, so
// bare-term references in the proof don't typecheck against both.
proof fn mat_pow_fib(n: nat)
    ensures mat_pow((Mat2 { a: 1, b: 1, c: 1, d: 0 }), n + 1)
        == (Mat2 { a: fib(n + 2), b: fib(n + 1), c: fib(n + 1), d: fib(n) })
    decreases n
by {
    if h : n = 0 then (
        subst h
        -- Q^1 = Q·Q^0 = Q·I = Q = [[1,1],[1,0]] = [[F(2),F(1)],[F(1),F(0)]].
        have hq : mat_pow (Mat2.mk 1 1 1 0) (0 + 1) = Mat2.mk 1 1 1 0 := by
            conv_lhs => unfold mat_pow
            rw [if_neg (by omega : (0 + 1 : Nat) ≠ 0)]
            rw [show ((↑(0 + 1 : Nat) : Int) - 1).toNat = 0 from by omega]
            conv_lhs => rw [show mat_pow (Mat2.mk 1 1 1 0) 0 = Mat2.mk 1 0 0 1 from by unfold mat_pow; simp]
            simp [mat_mul]
        have f0 : fib 0 = 0 := by unfold fib; simp
        have f1 : fib (0 + 1) = 1 := by unfold fib; simp
        have f2 : fib (0 + 2) = 1 := by
            unfold fib
            rw [if_neg (by omega : (0 + 2 : Nat) ≠ 0), if_neg (by omega : (0 + 2 : Nat) ≠ 1)]
            rw [show ((↑(0 + 2 : Nat) : Int) - 1).toNat = 1 from by omega]
            rw [show ((↑(0 + 2 : Nat) : Int) - 2).toNat = 0 from by omega]
            unfold fib; simp
        rw [hq, f0, f1, f2]
    ) else (
        have ih := mat_pow_fib (n - 1)
        have e_idx1 : (n - 1) + 1 = n := by omega
        have e_idx2 : (n - 1) + 2 = n + 1 := by omega
        rw [e_idx1, e_idx2] at ih
        -- ih : mat_pow Q n = Mat2.mk (fib (n+1)) (fib n) (fib n) (fib (n-1))
        have hstep : mat_pow (Mat2.mk 1 1 1 0) (n + 1)
                = mat_mul (Mat2.mk 1 1 1 0) (mat_pow (Mat2.mk 1 1 1 0) n) := by
            conv_lhs => unfold mat_pow
            rw [if_neg (by omega : (n + 1 : Nat) ≠ 0)]
            rw [show ((↑(n + 1 : Nat) : Int) - 1).toNat = n from by omega]
        have rec1 : fib (n + 2) = fib (n + 1) + fib n := by
            conv_lhs => unfold fib
            rw [if_neg (by omega : (n + 2 : Nat) ≠ 0), if_neg (by omega : (n + 2 : Nat) ≠ 1)]
            rw [show ((↑(n + 2 : Nat) : Int) - 1).toNat = n + 1 from by omega]
            rw [show ((↑(n + 2 : Nat) : Int) - 2).toNat = n from by omega]
        have rec2 : fib (n + 1) = fib n + fib (n - 1) := by
            conv_lhs => unfold fib
            rw [if_neg (by omega : (n + 1 : Nat) ≠ 0), if_neg (by omega : (n + 1 : Nat) ≠ 1)]
            rw [show ((↑(n + 1 : Nat) : Int) - 1).toNat = n from by omega]
            rw [show ((↑(n + 1 : Nat) : Int) - 2).toNat = n - 1 from by omega]
        rw [hstep, ih]
        simp [mat_mul, Mat2.mk.injEq]
        omega
    )
}

// ── The unification with Chapter 5 ──────────────────────────────────────────
// Matrix multiplication is associative (pure algebra on the 8 entries — `ring`
// per component). This is what makes "by squaring" sound: the monoid law.
proof fn mat_mul_assoc(x: Mat2, y: Mat2, z: Mat2)
    ensures mat_mul(mat_mul(x, y), z) == mat_mul(x, mat_mul(y, z))
by {
    simp only [mat_mul, Mat2.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
}

// mat_pow(M·M, k) == mat_pow(M, 2k). This is *exactly* Chapter 5's `pow_square`
// with scalar `*` replaced by `mat_mul` — the lemma that lets the by-squaring
// loop replace M^e by (M·M)^(e/2). Where ch5 closed with `ring` (nat mul is
// associative *and* commutative), here we close with `mat_mul_assoc` alone
// (matrix mul is associative but NOT commutative — and associativity is all
// squaring needs).
proof fn mat_pow_square(m: Mat2, k: nat)
    ensures mat_pow(mat_mul(m, m), k) == mat_pow(m, 2 * k)
    decreases k
by {
    if h : k = 0 then (
        subst h
        simp [mat_pow]
    ) else (
        have ih := mat_pow_square m (k - 1)
        conv_lhs => unfold mat_pow
        rw [if_neg (by omega : k ≠ 0)]
        rw [show ((↑k : Int) - 1).toNat = k - 1 from by omega]
        conv_rhs => unfold mat_pow
        rw [if_neg (by omega : 2 * k ≠ 0)]
        rw [show ((↑(2 * k) : Int) - 1).toNat = 2 * k - 1 from by omega]
        conv_rhs => unfold mat_pow
        rw [if_neg (by omega : 2 * k - 1 ≠ 0)]
        rw [show ((↑(2 * k - 1) : Int) - 1).toNat = 2 * (k - 1) from by omega]
        rw [ih]
        exact mat_mul_assoc m m (mat_pow m (2 * (k - 1)))
    )
}

fn main() {}

} // verus!
