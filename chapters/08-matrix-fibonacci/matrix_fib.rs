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

// Identity [[1,0],[0,1]] is a left unit (for mat_pow_add's base case).
proof fn mat_id_left_lit(x: Mat2)
    ensures mat_mul((Mat2 { a: 1, b: 0, c: 0, d: 1 }), x) == x
by { simp [mat_mul] }

// M^i · M^j = M^(i+j). The exponent law: it's what lets the squaring step
// "Q^g · Q^g = Q^(2g)" double the exponent. Induction on i (assoc in the step).
proof fn mat_pow_add(m: Mat2, i: nat, j: nat)
    ensures mat_mul(mat_pow(m, i), mat_pow(m, j)) == mat_pow(m, i + j)
    decreases i
by {
    if h : i = 0 then (
        subst h
        have h0 : mat_pow m 0 = Mat2.mk 1 0 0 1 := by unfold mat_pow; simp
        rw [h0, show (0 : Nat) + j = j from by omega]
        exact mat_id_left_lit (mat_pow m j)
    ) else (
        have ih := mat_pow_add m (i - 1) j
        have hi : mat_pow m i = mat_mul m (mat_pow m (i - 1)) := by
            conv_lhs => unfold mat_pow
            rw [if_neg (by omega : i ≠ 0)]
            rw [show ((↑i : Int) - 1).toNat = i - 1 from by omega]
        have hij : mat_pow m (i + j) = mat_mul m (mat_pow m ((i - 1) + j)) := by
            conv_lhs => unfold mat_pow
            rw [if_neg (by omega : i + j ≠ 0)]
            rw [show ((↑(i + j) : Int) - 1).toNat = (i - 1) + j from by omega]
        rw [hi, mat_mul_assoc, ih, hij]
    )
}

// Monotonicity of fib (reproduced from ch7). Bounds the matrix entries for the
// overflow checks: every entry of Q^g is some F(index <= n+1) <= F(n+1).
proof fn fib_mono(k: nat, m: nat)
    requires k <= m
    ensures fib(k) <= fib(m)
    decreases m - k
by {
    if h : k = m then (
        subst h; omega
    ) else (
        have ih := fib_mono k (m - 1)
        have ih_app := ih (by omega)
        have step : fib (m - 1) <= fib m := by
            if hm1 : m = 1 then (
                subst hm1
                have f0 : fib 0 = 0 := by unfold fib; simp
                have f1 : fib 1 = 1 := by unfold fib; simp
                show fib 0 ≤ fib 1
                omega
            ) else (
                have hrec : fib m = fib (m - 1) + fib (m - 2) := by
                    conv_lhs => unfold fib
                    rw [if_neg (by omega : m ≠ 0)]
                    rw [if_neg (by omega : m ≠ 1)]
                    rw [show ((↑m : Int) - 1).toNat = m - 1 from by omega]
                    rw [show ((↑m : Int) - 2).toNat = m - 2 from by omega]
                omega
            )
        omega
    )
}

// ── The executable layer ────────────────────────────────────────────────────
// An exec 2x2 matrix of u64, with a spec `view` into the ghost `Mat2`.
struct M { a: u64, b: u64, c: u64, d: u64 }

spec fn view(m: M) -> Mat2 {
    Mat2 { a: m.a as nat, b: m.b as nat, c: m.c as nat, d: m.d as nat }
}

// Executable matrix product. With every entry <= 2^31, each scalar product is
// <= 2^62 and each output entry (a sum of two) <= 2^63 < 2^64, so nothing
// overflows u64. `view(mmul x y) == mat_mul(view x, view y)`.
#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; constructor <;> nlinarith) | (intros; rw [Int.toNat_add (by nlinarith) (by nlinarith), Int.toNat_mul, Int.toNat_mul] <;> try omega) | (intros; nlinarith) | (intros; omega)")]
fn mmul(x: M, y: M) -> (r: M)
    requires
        x.a <= 0x8000_0000, x.b <= 0x8000_0000, x.c <= 0x8000_0000, x.d <= 0x8000_0000,
        y.a <= 0x8000_0000, y.b <= 0x8000_0000, y.c <= 0x8000_0000, y.d <= 0x8000_0000,
    ensures
        r.a as nat == (x.a as nat) * (y.a as nat) + (x.b as nat) * (y.c as nat),
        r.b as nat == (x.a as nat) * (y.b as nat) + (x.b as nat) * (y.d as nat),
        r.c as nat == (x.c as nat) * (y.a as nat) + (x.d as nat) * (y.c as nat),
        r.d as nat == (x.c as nat) * (y.b as nat) + (x.d as nat) * (y.d as nat),
{
    M {
        a: x.a * y.a + x.b * y.c,
        b: x.a * y.b + x.b * y.d,
        c: x.c * y.a + x.d * y.c,
        d: x.c * y.b + x.d * y.d,
    }
}

fn main() {}

} // verus!
