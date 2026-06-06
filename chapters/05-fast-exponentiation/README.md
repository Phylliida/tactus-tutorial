# Chapter 5: Exponentiation by squaring

> **Claim.** The iterative Rust function `pow_iter(base, exp)` computes `base^exp` in **O(log exp)** multiplications, matches the recursive definition `pow`, and never overflows — for every `base ≥ 1` with `base^exp ≤ 2³¹`.

This is the capstone. Chapter 1 verified a loop against a *closed-form* identity; Chapter 4 verified a loop against a *recursive, linear* spec (`factorial`). Here we close the loop the whole tutorial has been pointing at: a loop that is **exponentially faster** than its spec, proven to compute exactly the same value.

The full code is in [`pow_by_squaring.rs`](pow_by_squaring.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus --lean-backend pow_by_squaring.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## The specification

```rust
spec fn pow(base: nat, e: nat) -> nat
    decreases e
{
    if e == 0 { 1 } else { base * pow(base, (e - 1) as nat) }
}
```

The naive reading is an O(e) algorithm: to compute `base^e`, multiply `base` by itself `e` times. That's the *spec*. The *implementation* will be cleverer.

## The fast algorithm

Exponentiation by squaring computes `base^exp` in O(log exp) steps using one observation:

> `base^e = (base²)^(e/2)` when `e` is even, and `base^e = base · (base²)^(e/2)` when `e` is odd.

So instead of stepping the exponent down by 1 each iteration, we **halve** it — squaring the base as we go. `2^60` needs 60 multiplications the naive way; squaring does it in 6.

```rust
let mut result: u64 = 1;
let mut b: u64 = base;
let mut e: u64 = exp;
while e > 0 {
    if e % 2 == 1 { result = result * b; }
    b = b * b;
    e = e / 2;
}
```

`b` holds the running square `base^(2^k)`; `result` accumulates the factors that correspond to the 1-bits of `exp`; `e` is the exponent being shifted right.

## The invariant

The whole proof hangs on one loop invariant:

```rust
result * pow(b, e) == pow(base, exp)
```

"What we've accumulated, times what's left to compute, equals the answer." At the start, `result = 1` and `b = base`, `e = exp`, so it's `1 · pow(base, exp) = pow(base, exp)`. At the end, `e == 0`, so `pow(b, 0) = 1` and the invariant collapses to `result = pow(base, exp)` — the postcondition.

## Three helper lemmas

### `pow_pos` and `pow_ge_base`

```rust
proof fn pow_pos(base: nat, e: nat)      requires base >= 1  ensures pow(base, e) >= 1
proof fn pow_ge_base(base: nat, e: nat)  requires base >= 1, e >= 1  ensures pow(base, e) >= base
```

Both are self-recursive (the strong-induction shape from Chapter 3). They exist for the **overflow** argument: in the loop body `b ≤ pow(b, e) ≤ result · pow(b, e) = pow(base, exp) ≤ 2³¹`, so `b·b ≤ 2⁶²` fits in `u64`. `pow_ge_base` supplies the `b ≤ pow(b, e)` step.

### `pow_square` — the crux

```rust
proof fn pow_square(base: nat, k: nat)
    ensures pow(base * base, k) == pow(base, 2 * k)
    decreases k
```

This is the lemma that makes the algorithm work: it says squaring the base and halving the exponent leaves the value unchanged. The proof is induction on `k`: the left side unfolds once to `(base·base) · pow(base·base, k−1)`; the right side unfolds **twice** to `base · base · pow(base, 2(k−1))`; the induction hypothesis bridges them, and `ring` finishes the algebra.

With `pow_square` in hand, each loop step rewrites `pow(b, e)` in terms of `pow(b·b, e/2)`: in the even case directly (`2·(e/2) = e`), in the odd case via the recurrence (`pow(b,e) = b · pow(b, e−1)` and `2·(e/2) = e−1`).

## The loop, verified

```rust
#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; omega) | (intros; nlinarith)")]
fn pow_iter(base: u64, exp: u64) -> (r: u64)
    requires base >= 1, pow(base as nat, exp as nat) <= 0x8000_0000
    ensures r as nat == pow(base as nat, exp as nat)
```

Two pieces beyond Chapter 4's template:

**The closer.** `pow_iter` extends the default closer with two fallbacks:
- `(intros; omega)` — `omega` discharges the *linear* obligations and, crucially, **bridges ℕ and ℤ** (the loop variables are `u64`/`ℤ` but `pow` is `nat`/`ℕ`-valued). It abstracts nonlinear products like `b*b` as opaque atoms, so a goal like `b*b ≤ 2⁶² ⊢ b*b < 2⁶⁴` closes.
- `(intros; nlinarith)` — for the genuinely nonlinear obligations `omega` can't touch.

**The loop-body assert chain** feeds the maintain step the facts it needs:

```rust
{
    assert(b as nat <= pow(base as nat, exp as nat)) by { … };   // (A) for the b*b bound
    assert(b * b <= 0x4000_0000_0000_0000) by { … };             // (B) b*b fits (concrete bound)
    if e % 2 == 1 {
        assert((result * b) as nat * pow((b*b) as nat, (e/2) as nat) == …) by { … };  // odd maintain
        assert(result * b <= 0x8000_0000) by { … };              // result*b fits
        assert(0 <= result * b) by { … };                        // overflow lower bound
        result = result * b;
    } else {
        assert((result as nat) * pow((b*b) as nat, (e/2) as nat) == …) by { … };       // even maintain
    }
    assert(0 <= b * b) by { … };                                 // overflow lower bound
    b = b * b;
    e = e / 2;
}
```

Each maintain assert uses `pow_square` (plus the recurrence in the odd case) to rewrite `pow(b·b, e/2)` back to `pow(b, e)`, after which the invariant equation matches. The overflow asserts establish *both* bounds (the upper from `pow_ge_base`/`pow_square`, the lower from `0 ≤ result, 0 ≤ b`) so the auto-generated overflow checks close via the closer.

## Why this would be painful in Z3

Everything from chapters 1–4 — no native induction, so `pow_pos`, `pow_ge_base`, and especially `pow_square` would each need hand-rolled recursive proofs with `reveal_with_fuel` tuning. `pow_square` is the sticking point: it's a statement about `pow` at *two different bases* (`base` and `base·base`) related by a *doubled exponent*, exactly the kind of nested-recursion identity that sends heuristic unrolling into the weeds. Lean proves it by structural induction in a handful of lines.

## Why this is the whole point

Look back at Chapter 1. `sum_iter` was the *same* value as the recursive `sum_to`, computed by a loop — but it wasn't *faster*, just iterative. Here the implementation is **exponentially faster** than its specification, and the verification proves they agree on every input in range.

That's the promise of this style of verification, stated as plainly as it gets: **you can optimize aggressively without giving up correctness.** Write the obviously-correct spec; write the fast implementation; prove they're equal once; and every future refactor that breaks the equality fails to verify before it ships. The spec stays readable, the code stays fast, and the proof keeps them honest with each other.

## Exercises

1. **Lower the precondition's cost.** The precondition `pow(base, exp) ≤ 2³¹` is conservative. Trace why the loop's intermediate `b` can momentarily exceed the final answer (it holds `base^(2^k)`), and convince yourself the bound is about the *in-body* `b`, not the result. Could a `u128` accumulator relax it?
2. **`pow(base, 0) == 1` and `pow(base, 1) == base`.** Two one-liners; good warm-ups for the `unfold`/`simp` rhythm.
3. **Modular exponentiation.** Define `pow_mod(base, exp, m) = pow(base, exp) % m` and write an iterative version that reduces mod `m` each step (`result = (result * b) % m`). The overflow story gets *easier* (everything stays below `m`), but the invariant becomes a congruence — a genuinely different flavor of proof. This is the algorithm behind RSA.

## What's next

This is the current end of the tutorial. The natural continuations all reuse this chapter's structure: the **Euclidean gcd** (verified to equal the spec gcd), **fast-doubling Fibonacci** (the O(log n) algorithm that Chapter 3's addition formula was built to unlock), or a return to **combinatorial identities** (Pascal's rule, the binomial theorem) for the Sage-flavored reader. Each is a recurrence-based invariant, a few helper lemmas, and an assert chain in the loop body — the template you now have in hand.
