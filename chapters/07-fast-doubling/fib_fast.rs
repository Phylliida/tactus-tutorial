// Chapter 7: fast-doubling Fibonacci — an O(log n) algorithm verified against
// the recursive `fib` spec. The Fibonacci thread's capstone.
//
// `fast_fib(n)` returns the pair (F(n), F(n+1)) by recursing on k = n/2, using
// the two doubling identities (both from Chapter 3's addition formula
// F_{m+n+1} = F_m·F_n + F_{m+1}·F_{n+1}):
//   odd:  F_{2k+1} = F_k² + F_{k+1}²              (addition formula at m = n = k)
//   even: F_{2k}   = F_k · (2·F_{k+1} − F_k)      (needs F_k ≤ F_{k+1}, i.e. fib_mono)
//
// Helpers (verified): fib_addition (reproduced from Chapter 3) and fib_mono
// (mirrors Chapter 4's fact_monotone). The recursive exec fn `fast_fib` then
// verifies its postconditions via four asserts — one per (parity × component) —
// each establishing the relevant doubling identity over ℤ (so the `2b − a`
// subtraction is exact, no nat truncation) and converting back via c, d ≥ 0.
//
// Two things worth knowing for anyone editing the proof:
//   - Inside `by { … }` blocks the text is raw Lean: use `.toNat`, never the
//     Verus `as nat` (a parse error in Lean).
//   - The F(2k+1) asserts close `d = ↑F(2k+1)` with `omega` (it atomizes the
//     fib products and reads the cast identity linearly); the F(2k)/F(2k+2)
//     asserts genuinely expand `a·(2b−a)`, so they need `nlinarith`. Using
//     `nlinarith` for the former whnf-loops on `fib`. The whole-fn proof is
//     large, hence the raised `heartbeats`.

use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

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
                show fib 0 ≤ fib 1   -- defeq `1 - 1 ≡ 0`, so omega's atoms match f0/f1
                omega
            ) else (
                -- m >= 2: fib m = fib(m-1) + fib(m-2) >= fib(m-1) (fib(m-2) >= 0).
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
// The `else` branch (a == F(k), b == F(k+1)) builds the doubling identities from:
//   - fib_addition(k, k):     F(2k+1) = a² + b²                 (subscript k+k+1)
//   - fib_addition(k, k+1):   F(2k+2) = a·b + b·F(k+2)          (subscript k+(k+1)+1)
//                             and F(k+2) = F(k+1) + F(k) gives  F(2k+2) = 2ab + b²
//                             so c+d = a·(2b−a) + (a²+b²) = 2ab + b² = F(2k+2)
//   - F(2k) = c = a·(2b−a) follows over ℤ (the subtraction is exact there;
//     nat-safe since fib_mono ⟹ a ≤ b), giving c = F(2k+2) − F(2k+1).
//   even (n=2k):    (c, d) = (F(2k), F(2k+1))
//   odd  (n=2k+1):  (d, c+d) = (F(2k+1), F(2k+2))
// The whole-fn closer discharges the product-overflow checks (a*a, b*b,
// a*(2*b-a)) from the `a <= b <= 2^31` bounds; `omega` handles the linear/cast
// obligations and the loop decrease.
#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; omega) | (intros; nlinarith)")]
#[verifier::heartbeats(4000000)]
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
        // (k + 1 <= n + 1, since k = n/2 and n >= 1).
        assert(fib((k + 1) as nat) <= 0x8000_0000) by {
            -- k := n/2 is a trailing goal-position let; name it explicitly (plain
            -- `intros` leaves it inaccessible here). The four `_` are
            -- decrease_init0 and the n=0 / 2≠0 / 2≠0 guards before it.
            intro _ _ _ _ k
            have hm := fib_mono ((k + 1).toNat) ((n + 1).toNat) (by omega);
            omega
        };
        let (a, b) = fast_fib(k);   // a.toNat == fib k.toNat, b.toNat == fib (k+1).toNat
        // Bounds for overflow + the 2*b-a nat-safety. b = F(k+1) <= F(n+1) <= 2^31
        // (via fib_mono + the precondition h_req0), and a = F(k) <= F(k+1) = b.
        // (`a`/`b` come from a tuple-let destructuring, so they're let-bound
        // fvars (a := tmp.1 ← ret.1); omega/simp_all won't see through those.
        // `simp only [<the lets>]` unfolds them to the `_tactus_ret_8` the
        // recursive call's ensures are stated over, then omega closes.)
        assert(b <= 0x8000_0000) by {
            intros
            have hm := fib_mono ((k + 1).toNat) ((n + 1).toNat) (by omega);
            simp only [a, b, tmp___0] at *
            omega
        };
        assert(a <= b) by {
            intros
            have hmono := fib_mono (k.toNat) ((k + 1).toNat) (by omega);
            simp only [a, b, tmp___0] at *
            omega
        };
        // Overflow bounds for the two products (concrete 2^63 literals, both
        // < 2^64, so the auto overflow conjunctions close via omega treating the
        // product as an atom). With a <= b <= 2^31: a*a+b*b <= 2^63 and
        // a*(2*b-a) <= 2*a*b <= 2^63. nlinarith does the product; the lower
        // bounds keep the `0 <= _` halves honest.
        assert(a * a <= 0x4000_0000_0000_0000) by { intros; nlinarith };
        assert(0 <= a * a) by { intros; nlinarith };
        assert(b * b <= 0x4000_0000_0000_0000) by { intros; nlinarith };
        assert(0 <= b * b) by { intros; nlinarith };
        assert(a * a + b * b <= 0x8000_0000_0000_0000) by { intros; nlinarith };
        assert(0 <= a * a + b * b) by { intros; nlinarith };
        assert(a * (2 * b - a) <= 0x8000_0000_0000_0000) by { intros; nlinarith };
        assert(0 <= a * (2 * b - a)) by { intros; nlinarith };
        // c = F(2k), d = F(2k+1). `2*b - a` is nat-safe (a <= b <= 2*b).
        let c = a * (2 * b - a);
        let d = a * a + b * b;
        if n % 2 == 0 {
            // n = 2k: (F(n), F(n+1)) = (F(2k), F(2k+1)).
            // F(2k+1) = F(k)^2 + F(k+1)^2  (fib_addition at m=n=k).
            assert(d as nat == fib((n + 1) as nat)) by {
                intros
                have e1 : (a : Int) = ↑(fib (k.toNat)) := by simp only [a, tmp___0]; omega
                have e2 : (b : Int) = ↑(fib ((k + 1).toNat)) := by simp only [b, tmp___0]; omega
                have hd_def : (d : Int) = a * a + b * b := by simp only [d, tmp__3]
                have hd0 : (0 : Int) <= a * a + b * b := by omega
                have hadd := fib_addition (k.toNat) (k.toNat);
                have hk1 : k.toNat + 1 = (k + 1).toNat := by omega
                rw [hk1] at hadd
                have haddZ : (fib (k.toNat + k.toNat + 1) : Int) = ↑(fib k.toNat) * ↑(fib k.toNat) + ↑(fib ((k + 1).toNat)) * ↑(fib ((k + 1).toNat)) := by exact_mod_cast hadd
                have hdZ : (d : Int) = ↑(fib (k.toNat + k.toNat + 1)) := by rw [hd_def, e1, e2]; omega
                rw [show k.toNat + k.toNat + 1 = (n + 1).toNat from by omega] at hdZ
                omega
            };
            // F(2k) = F(k)·(2·F(k+1) − F(k)) = c. We avoid bridging c's nat
            // subtraction directly: prove the ℤ identity c = ↑F(2k) using
            // F(2k) = F(2k+2) − F(2k+1) (recurrence) with F(2k+1), F(2k+2) from
            // fib_addition, then convert via c ≥ 0.
            assert(c as nat == fib(n as nat)) by {
                intros
                have e1 : (a : Int) = ↑(fib (k.toNat)) := by simp only [a, tmp___0]; omega
                have e2 : (b : Int) = ↑(fib ((k + 1).toNat)) := by simp only [b, tmp___0]; omega
                have hc_def : (c : Int) = a * (2 * b - a) := by simp only [c, tmp__2]
                have hc0 : (0 : Int) <= a * (2 * b - a) := by nlinarith
                have h1 := fib_addition (k.toNat) (k.toNat);
                have h2 := fib_addition (k.toNat) (k.toNat + 1);
                have hk1 : k.toNat + 1 = (k + 1).toNat := by omega
                have hr : fib (k.toNat + 1 + 1) = fib (k.toNat + 1) + fib (k.toNat) := by
                    conv_lhs => unfold fib
                    rw [if_neg (by omega : (k.toNat + 1 + 1 : Nat) ≠ 0), if_neg (by omega : (k.toNat + 1 + 1 : Nat) ≠ 1)]
                    rw [show ((↑(k.toNat + 1 + 1) : Int) - 1).toNat = k.toNat + 1 from by omega]
                    rw [show ((↑(k.toNat + 1 + 1) : Int) - 2).toNat = k.toNat from by omega]
                have hrec : fib (k.toNat + k.toNat + 1 + 1) = fib (k.toNat + k.toNat + 1) + fib (k.toNat + k.toNat) := by
                    conv_lhs => unfold fib
                    rw [if_neg (by omega : (k.toNat + k.toNat + 1 + 1 : Nat) ≠ 0), if_neg (by omega : (k.toNat + k.toNat + 1 + 1 : Nat) ≠ 1)]
                    rw [show ((↑(k.toNat + k.toNat + 1 + 1) : Int) - 1).toNat = k.toNat + k.toNat + 1 from by omega]
                    rw [show ((↑(k.toNat + k.toNat + 1 + 1) : Int) - 2).toNat = k.toNat + k.toNat from by omega]
                rw [show k.toNat + (k.toNat + 1) + 1 = k.toNat + k.toNat + 1 + 1 from by omega] at h2
                rw [hr] at h2
                rw [hk1] at h1 h2
                have h1Z : (fib (k.toNat + k.toNat + 1) : Int) = ↑(fib k.toNat) * ↑(fib k.toNat) + ↑(fib ((k + 1).toNat)) * ↑(fib ((k + 1).toNat)) := by exact_mod_cast h1
                have h2Z : (fib (k.toNat + k.toNat + 1 + 1) : Int) = ↑(fib k.toNat) * ↑(fib ((k + 1).toNat)) + ↑(fib ((k + 1).toNat)) * (↑(fib ((k + 1).toNat)) + ↑(fib k.toNat)) := by exact_mod_cast h2
                have hrecZ : (fib (k.toNat + k.toNat + 1 + 1) : Int) = ↑(fib (k.toNat + k.toNat + 1)) + ↑(fib (k.toNat + k.toNat)) := by exact_mod_cast hrec
                -- `c = F(2k)` is a polynomial identity in F(k), F(k+1): with the
                -- three product hyps below, F(2k) = F(2k+2) − F(2k+1) gives
                -- a·(2b−a) exactly. `linear_combination` (targeted `ring`) closes
                -- it directly — bare `nlinarith [h1Z,h2Z,hrecZ]` instead folds the
                -- three fib-product hints over the whole context and blows the
                -- interpreter stack (deep-recursion abort).
                have hcZ : (c : Int) = ↑(fib (k.toNat + k.toNat)) := by
                    rw [hc_def, e1, e2]; linear_combination h1Z - h2Z + hrecZ
                have hn : k.toNat + k.toNat = n.toNat := by omega
                rw [hn] at hcZ
                omega
            };
            (c, d)
        } else {
            // n = 2k+1: (F(n), F(n+1)) = (F(2k+1), F(2k+2)).
            // F(n) = F(2k+1) = F(k)^2 + F(k+1)^2 = d  (same identity as even-d).
            assert(d as nat == fib(n as nat)) by {
                intros
                have e1 : (a : Int) = ↑(fib (k.toNat)) := by simp only [a, tmp___0]; omega
                have e2 : (b : Int) = ↑(fib ((k + 1).toNat)) := by simp only [b, tmp___0]; omega
                have hd_def : (d : Int) = a * a + b * b := by simp only [d, tmp__3]
                have hd0 : (0 : Int) <= a * a + b * b := by omega
                have hadd := fib_addition (k.toNat) (k.toNat);
                have hk1 : k.toNat + 1 = (k + 1).toNat := by omega
                rw [hk1] at hadd
                have haddZ : (fib (k.toNat + k.toNat + 1) : Int) = ↑(fib k.toNat) * ↑(fib k.toNat) + ↑(fib ((k + 1).toNat)) * ↑(fib ((k + 1).toNat)) := by exact_mod_cast hadd
                have hdZ : (d : Int) = ↑(fib (k.toNat + k.toNat + 1)) := by rw [hd_def, e1, e2]; omega
                rw [show k.toNat + k.toNat + 1 = n.toNat from by omega] at hdZ
                omega
            };
            // F(n+1) = F(2k+2) = c + d.  c+d = a*(2b-a)+(a²+b²) = 2ab+b² over ℤ;
            // = F(k)·F(k+1) + F(k+1)·F(k+2) with F(k+2)=F(k+1)+F(k) (fib_addition + recurrence).
            assert((c + d) as nat == fib((n + 1) as nat)) by {
                intros
                have e1 : (a : Int) = ↑(fib (k.toNat)) := by simp only [a, tmp___0]; omega
                have e2 : (b : Int) = ↑(fib ((k + 1).toNat)) := by simp only [b, tmp___0]; omega
                have hcd_def : (c + d : Int) = a * (2 * b - a) + (a * a + b * b) := by simp only [c, d, tmp__2, tmp__3]
                have h2 := fib_addition (k.toNat) (k.toNat + 1);
                have hk1 : k.toNat + 1 = (k + 1).toNat := by omega
                have hr : fib (k.toNat + 1 + 1) = fib (k.toNat + 1) + fib (k.toNat) := by
                    conv_lhs => unfold fib
                    rw [if_neg (by omega : (k.toNat + 1 + 1 : Nat) ≠ 0), if_neg (by omega : (k.toNat + 1 + 1 : Nat) ≠ 1)]
                    rw [show ((↑(k.toNat + 1 + 1) : Int) - 1).toNat = k.toNat + 1 from by omega]
                    rw [show ((↑(k.toNat + 1 + 1) : Int) - 2).toNat = k.toNat from by omega]
                rw [show k.toNat + (k.toNat + 1) + 1 = k.toNat + k.toNat + 1 + 1 from by omega] at h2
                rw [hr] at h2
                rw [hk1] at h2
                have h2Z : (fib (k.toNat + k.toNat + 1 + 1) : Int) = ↑(fib k.toNat) * ↑(fib ((k + 1).toNat)) + ↑(fib ((k + 1).toNat)) * (↑(fib ((k + 1).toNat)) + ↑(fib k.toNat)) := by exact_mod_cast h2
                have hcdZ : (c + d : Int) = ↑(fib (k.toNat + k.toNat + 1 + 1)) := by rw [hcd_def, e1, e2]; nlinarith [h2Z]
                rw [show k.toNat + k.toNat + 1 + 1 = (n + 1).toNat from by omega] at hcdZ
                omega
            };
            (d, c + d)
        }
    }
}

fn main() {}

} // verus!
