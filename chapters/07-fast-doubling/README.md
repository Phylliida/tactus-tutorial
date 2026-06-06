# Chapter 7: Fast-doubling Fibonacci

> **Claim.** The recursive Rust function `fast_fib(n)` computes the pair
> `(F(n), F(n+1))` in **O(log n)** arithmetic operations — exponentially fewer
> than the naive O(n) recurrence — and matches the spec `fib`.

This is the Fibonacci thread's capstone, and the payoff Chapter 3 was built for.
Chapter 3 proved the **addition formula**

```
F_{m+n+1} = F_m·F_n + F_{m+1}·F_{n+1}
```

and noted that it "opens the door to an O(log n) Fibonacci algorithm." This is
that door. Where Chapter 5 made *exponentiation* logarithmic by squaring, this
chapter makes *Fibonacci* logarithmic by **doubling** — computing `F(2k)` and
`F(2k+1)` directly from `F(k)` and `F(k+1)`, so each step roughly doubles the
index instead of incrementing it.

The full code is in [`fib_fast.rs`](fib_fast.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus --lean-backend fib_fast.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## The two doubling identities

Both fall out of Chapter 3's addition formula `F_{m+n+1} = F_m·F_n + F_{m+1}·F_{n+1}`.

**Odd index — set `m = n = k`:**

```
F_{2k+1} = F_k² + F_{k+1}²
```

Clean, symmetric, subtraction-free. This is the addition formula at `m = n = k`
verbatim: `F_{k+k+1} = F_k·F_k + F_{k+1}·F_{k+1}`.

**Even index:**

```
F_{2k} = F_k · (2·F_{k+1} − F_k)
```

This one has a subtraction, and over `nat` that's a wrinkle: it's only the true
value when `2·F_{k+1} ≥ F_k`. That holds because Fibonacci is non-decreasing
(`F_k ≤ F_{k+1}`), so `2·F_{k+1} ≥ F_{k+1} ≥ F_k`. We prove `fib` monotone
(`fib_mono`) and use it both to justify the spec identity over `nat` and to keep
the `u64` subtraction `2*b - a` from underflowing.

> A subtraction-free way to state the even identity, if you prefer to avoid the
> monotonicity detour, is `F_{2k} + F_k² = 2·F_k·F_{k+1}` — the same fact with
> the `−F_k²` moved to the other side. The implementation still subtracts, so we
> keep the monotonicity lemma either way.

## The algorithm

`fast_fib(n)` returns the pair `(F(n), F(n+1))`, recursing on `k = n / 2`:

```rust
fn fast_fib(n: u64) -> (res: (u64, u64))   // (F(n), F(n+1))
    decreases n
{
    if n == 0 {
        (0, 1)                       // (F(0), F(1)) = (0, 1)
    } else {
        let (a, b) = fast_fib(n / 2); // a = F(k), b = F(k+1),  k = n/2
        let c = a * (2 * b - a);      // F(2k)
        let d = a * a + b * b;        // F(2k+1)
        if n % 2 == 0 {
            (c, d)                    // n = 2k:   (F(n), F(n+1)) = (F(2k),   F(2k+1))
        } else {
            (d, c + d)                // n = 2k+1: (F(n), F(n+1)) = (F(2k+1), F(2k+2))
        }
    }
}
```

The recursion depth is the bit-length of `n` — `O(log n)` — and each level does
a handful of multiplications. `2^60` Fibonacci numbers are reached in ~60 steps
the naive way; doubling reaches `F(2^60)` (astronomically far out) in 60 steps.
For `u64` the interesting range is small (`F(93)` is the last Fibonacci number
under `u64::MAX`), but the *asymptotics* are the point, and the verification
holds for every `n` in range.

### Why a recursive exec fn (not a loop)

The previous exec chapters (1, 4, 5) used `while` loops with a loop invariant.
Fast-doubling is naturally **recursive**: `F(n)` is defined in terms of
`F(n/2)`, and the post-processing (the even/odd `if`) happens *after* the
recursive call returns. So instead of a loop invariant we use a **recursive
postcondition** — `fast_fib` is verified against its own `ensures` clause, with
`decreases n` (the recursive call is on `n / 2 < n`, which `omega` handles since
the divisor `2` is a literal). This is the exec-mode mirror of the self-recursive
*proof* fns from Chapters 3 and 5.

## The proof obligations

Three things have to line up in the `else` branch, after `(a, b) = fast_fib(k)`
gives us `a == F(k)` and `b == F(k+1)`:

1. **The doubling identities**, instantiated at this `k`. We get them by calling
   the addition formula in proof mode — `fib_addition(k, k)` for the odd case —
   and `fib_mono` for the monotonicity that makes the even case's subtraction
   honest. (Calling a proof fn from an exec body is the `have _ := f args` form
   from Chapter 4.)
2. **The even/odd case split.** When `n = 2k` the answer is `(F(2k), F(2k+1))`;
   when `n = 2k+1` it's `(F(2k+1), F(2k+2))`, and `F(2k+2) = F(2k) + F(2k+1)` is
   one Fibonacci step (`c + d`). `omega` relates `n`, `k = n/2`, and `n % 2`;
   `nlinarith` handles the products in the identities.
3. **Overflow.** Every intermediate (`a*a`, `b*b`, `2*b - a`, `a*(2*b-a)`,
   `c + d`) must fit in `u64`. These are *products* of Fibonacci values, so the
   precondition bounds `F(n+1)` and the proof propagates that bound down — the
   fiddliest part, and the reason a real precondition is needed (as in
   Chapter 5).

## Why this would be brutal in Z3

Everything that made Chapters 3 and 5 hard, at once:

- **Nested recursion at a doubled index.** `F(2k)` related to `F(k)` is the
  `pow_square` situation (Chapter 5) but for a *two-term* recurrence — heuristic
  unrolling has no traction on "F at twice the index."
- **The identities are non-linear** (squares and products of `F` values), so
  even with the recurrence in hand the algebra needs `nlinarith`, not `omega`.
- **It rests on the addition formula**, which (Chapter 3) is itself a
  strong-induction proof Z3 won't attempt. Lean proves the formula once and this
  chapter *uses* it — composition of verified lemmas, which is exactly what a
  proof assistant is for and what an SMT solver is not.

## Exercises

1. **Drop the pair.** Write a `fib_single(n) -> u64` wrapper with
   `ensures r as nat == fib(n as nat)` that calls `fast_fib(n).0`. (One line of
   proof — the postcondition is the first component of `fast_fib`'s.)
2. **The subtraction-free even identity.** Reprove the even case using
   `F_{2k} + F_k² = 2·F_k·F_{k+1}` instead of `F_{2k} = F_k·(2F_{k+1} − F_k)`,
   and see whether it shortens the monotonicity argument.
3. **Matrix-power Fibonacci.** The other O(log n) Fibonacci comes from
   `[[1,1],[1,0]]^n`. Define 2×2 matrix multiplication, a `mat_pow` by squaring
   (Chapter 5's algorithm!), and prove the top-left entry is `F(n+1)`. This
   *unifies* this chapter with Chapter 5 — fast doubling is exactly matrix
   exponentiation with the redundant entries elided.

## What's next

This closes the Fibonacci arc: spec (ch2) → strong induction & the addition
formula (ch3) → the O(log n) algorithm that formula unlocks (ch7). The remaining
direction the tutorial points at is **combinatorics** — Pascal's rule, the
binomial theorem, hockey stick — the Sage-flavored thread, which needs a
binomial-coefficient spec and is proof-fn-first (closer to Chapter 3 than to the
exec chapters).
