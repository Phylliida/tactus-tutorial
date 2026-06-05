// Chapter 7: fast-doubling Fibonacci — an O(log n) algorithm verified against
// the recursive `fib` spec. The Fibonacci thread's capstone.
//
// STATUS: scaffold. The helper lemmas (fib_addition, fib_mono) mirror the
// VERIFIED Chapter 3 / Chapter 4 patterns and should be solid. The recursive
// exec fn `fast_fib` carries the algorithm and a best-effort proof, but its
// body has genuine unknowns that need a live Tactus run to settle:
//   (1) recursive *exec* fn support (decreases n; recursive call on n / 2);
//   (2) the even-index identity F(2k) = F(k)·(2·F(k+1) − F(k)), whose cleanest
//       derivation goes through fib_addition at a k-1 index — and the
//       dep-walker bug forbids a proof fn calling a sibling proof fn, so it's
//       derived *inline in the exec body* (exec fns may call proof fns);
//   (3) product-overflow bounds for a*a, b*b, a*(2*b - a), c + d.
// The exec fn's `else` branch carries the algorithm and a documented PROOF PLAN
// for the doubling-identity glue (its PROOF GAP); no `sorry`/`admit` is used —
// per the project's First Principles, the gap is left explicit rather than
// papered over, to be closed with a live verifier.
//
// The two doubling identities (both from Chapter 3's addition formula
// F_{m+n+1} = F_m·F_n + F_{m+1}·F_{n+1}):
//   odd:  F_{2k+1} = F_k² + F_{k+1}²              (addition formula at m = n = k)
//   even: F_{2k}   = F_k · (2·F_{k+1} − F_k)      (needs F_k ≤ F_{k+1}, i.e. fib_mono)

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

// ── The addition formula (verified in Chapter 3, reproduced here) ───────────
// F_{m+n+1} = F_m·F_n + F_{m+1}·F_{n+1}. Strong induction on m.
proof fn fib_addition(m: nat, n: nat)
    ensures fib(m + n + 1) == fib(m) * fib(n) + fib(m + 1) * fib(n + 1)
    decreases m
by {
    if h0 : m = 0 then (
        subst h0; unfold fib; simp
    ) else if h1 : m = 1 then (
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
        have h_m0 : ¬(m = 0) := by omega
        have h_m1 : ¬(m = 1) := by omega
        have ih1 := fib_addition (m - 1) n
        have ih2 := fib_addition (m - 2) n
        have e1a : (m - 1) + n + 1 = m + n := by omega
        have e1b : (m - 1) + 1 = m := by omega
        rw [e1a, e1b] at ih1
        have e2a : (m - 2) + n + 1 = m + n - 1 := by omega
        have e2b : (m - 2) + 1 = m - 1 := by omega
        rw [e2a, e2b] at ih2
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
        nlinarith [step_sum, ih1, ih2, step_m, step_m1]
    )
}

// ── Monotonicity: k <= m ==> fib(k) <= fib(m) ───────────────────────────────
// Mirrors Chapter 4's `fact_monotone`. Used for the even-identity subtraction
// guard (2·F(k+1) >= F(k)) and to propagate the overflow bound down the
// recursion (fib(k+1) <= fib(n+1)). Self-recursive; `decreases m - k`.
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
                omega
            ) else (
                // m >= 2: fib m = fib(m-1) + fib(m-2) >= fib(m-1) (fib(m-2) >= 0).
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

// ── The algorithm ───────────────────────────────────────────────────────────
// fast_fib(n) = (F(n), F(n+1)), recursing on k = n/2. O(log n).
//
// Precondition bounds F(n+1) at 2^31 so every product (a², b², a·2b) stays
// under 2^64. The bound propagates to the recursive call because k+1 <= n+1
// and fib is monotone (fib_mono).
//
// PROOF PLAN for the `else` branch (to be completed under a live Tactus — see
// the file header for why it's a plan, not blind proof text). With a == F(k),
// b == F(k+1), the facts come from three lemma instances + one unfold:
//   - fib_addition(k, k):     F(2k+1) = a² + b²                 (subscript k+k+1)
//   - fib_addition(k, k+1):   F(2k+2) = a·b + b·F(k+2)          (subscript k+(k+1)+1)
//                             and F(k+2) = F(k+1) + F(k) gives  F(2k+2) = 2ab + b²
//   - recurrence at 2k+2:     F(2k+2) = F(2k+1) + F(2k)    ⟹    F(2k) = 2ab − a²
//                             = a·(2b − a)  (nat-safe since fib_mono ⟹ a ≤ b)
//   even (n=2k):    (c, d) = (F(2k), F(2k+1))
//   odd  (n=2k+1):  (d, c+d) = (F(2k+1), F(2k) + F(2k+1)) = (F(2k+1), F(2k+2))
// `nlinarith` combines the products; `omega` relates n, k=n/2, n%2 and the casts.
#[verifier::tactus_auto]
fn fast_fib(n: u64) -> (res: (u64, u64))
    requires fib((n + 1) as nat) <= 0x8000_0000
    ensures
        res.0 as nat == fib(n as nat),
        res.1 as nat == fib((n + 1) as nat),
    decreases n
{
    if n == 0 {
        // (F(0), F(1)) = (0, 1).
        assert(fib(0 as nat) == 0) by { intros; unfold fib; simp };
        assert(fib(1 as nat) == 1) by { intros; unfold fib; simp };
        (0, 1)
    } else {
        let k = n / 2;
        // Recurse. The bound fib(k+1) <= fib(n+1) <= 2^31 comes from fib_mono
        // (k + 1 <= n + 1, since k = n/2 and n >= 1). This one we can attempt:
        // fib_mono gives the inequality, omega chains it with the precondition
        // (both fib(_) values are opaque atoms to omega).
        assert(fib((k + 1) as nat) <= 0x8000_0000) by {
            intros
            have hm := fib_mono ((k + 1) as nat) ((n + 1) as nat) (by omega);
            omega
        };
        let (a, b) = fast_fib(k);   // a == F(k), b == F(k+1)
        // c = F(2k), d = F(2k+1). `2*b - a` is nat-safe (2·F(k+1) >= F(k) by
        // fib_mono); products fit u64 since a, b <= 2^31.
        let c = a * (2 * b - a);
        let d = a * a + b * b;
        // PROOF GAP (see PROOF PLAN above): the postconditions of both arms
        // need the doubling-identity glue, which is the part to finish with a
        // live verifier. Until then this branch does not verify.
        if n % 2 == 0 {
            (c, d)        // n = 2k:   (F(n), F(n+1)) = (F(2k),   F(2k+1))
        } else {
            (d, c + d)    // n = 2k+1: (F(n), F(n+1)) = (F(2k+1), F(2k+2))
        }
    }
}

fn main() {}

} // verus!
