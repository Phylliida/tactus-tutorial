# Chapter 8: Matrix-power Fibonacci — the unification

> **Claim.** Computing `F(n+1)` as the top-left entry of `Q^n`, where
> `Q = [[1,1],[1,0]]` and `Q^n` is computed by **exponentiation by squaring**, is
> the *same algorithm* as Chapter 5 (fast exponentiation) and Chapter 7
> (fast-doubling Fibonacci). This chapter proves it.

Chapters 5 and 7 looked like two different clever tricks:

- **Chapter 5** made *exponentiation* logarithmic: `pow(b, e)` in O(log e) by
  squaring the base and halving the exponent, resting on
  `pow(b·b, k) = pow(b, 2k)`.
- **Chapter 7** made *Fibonacci* logarithmic: `fast_fib(n) = (F(n), F(n+1))` by
  doubling the index, resting on the addition formula.

They are the same trick. The Fibonacci recurrence is a **linear map**

```
[F(k+1), F(k)]  =  [[1,1],[1,0]] · [F(k), F(k-1)]
```

so `[F(n+1), F(n)] = Q^n · [F(1), F(0)]`, and `Q^n` itself is just
*exponentiation* — in the monoid of 2×2 matrices instead of the natural numbers.
Run Chapter 5's by-squaring algorithm there and you get Chapter 7, with the
redundant matrix entries elided.

The full code is in [`matrix_fib.rs`](matrix_fib.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus --lean-backend matrix_fib.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## The pieces

**The matrix.** A `Mat2` is `[[a,b],[c,d]]` over `nat`; `mat_mul` is the usual
product; `mat_pow(M, e)` is the *slow* recursive power (`M^0 = I`, `M^e = M ·
M^(e-1)`) — the exact shape of Chapter 5's `pow`, with `·` now matrix multiply.

**The Fibonacci identity** (`mat_pow_fib`). By induction on `n`:

```
Q^(n+1) = [[F(n+2), F(n+1)], [F(n+1), F(n)]]
```

(indices shifted by one so every entry is a genuine `nat` — no `F(-1)`). One
matrix step `Q · [[F(n+1),F(n)],[F(n),F(n-1)]]` folds to the next via two
Fibonacci recurrences. In particular the **top-left of `Q^n` is `F(n+1)`**
(`qpow_topleft`).

**The unification lemma** (`mat_pow_square`):

```
mat_pow(M·M, k) = mat_pow(M, 2k)
```

This is **Chapter 5's `pow_square`, character for character, with scalar `*`
replaced by `mat_mul`** — the lemma that lets "by squaring" double the exponent.
Where Chapter 5 closed the inductive step with `ring` (natural-number
multiplication is associative *and* commutative), here we close with
`mat_mul_assoc` alone: matrix multiplication is **associative but not
commutative**, and associativity is all that squaring needs. (We also prove the
companion exponent law `mat_pow_add`: `M^i · M^j = M^(i+j)`.)

## The algorithm

`qpow_exec(n)` computes `Q^n` by squaring, recursing on `n/2` — *exactly*
Chapter 7's `fast_fib`, but carrying the whole 2×2 matrix instead of the
`(F(k), F(k+1))` pair:

```rust
fn qpow_exec(n: u64) -> (r: M)        // view(r) == Q^n
    decreases n
{
    if n == 0 { I }                   // Q^0 = identity
    else {
        let half = qpow_exec(n / 2);  // Q^(n/2)
        let sq   = mmul(half, half);  // Q^(2·(n/2))
        if n % 2 == 1 { mmul(sq, Q) } // Q^(2·(n/2)+1) = Q^n
        else          { sq }          //  Q^(2·(n/2))  = Q^n
    }
}
```

`fib_matrix(n)` then just reads the top-left of `Q^n`. It verifies against the
recursive `mat_pow` spec via a `view` from the exec `M` (u64 entries) to the
ghost `Mat2` (nat entries) — the runtime-layer pattern.

## The proof obligations

1. **Correctness.** `view(qpow_exec(n)) == mat_pow(Q, n)`, by recursion on
   `n/2`. The squaring step uses `mat_pow_add` to show `Q^g · Q^g = Q^(2g)`; the
   odd step multiplies one more `Q`.
2. **Overflow.** Every `mmul` multiplies two entries `<= 2^31` (so each product
   `<= 2^62`, each sum `<= 2^63`). Why are the entries bounded? Each intermediate
   is a power `Q^(≤ n)`, and the entries of `Q^g` are Fibonacci numbers
   `F(g+1) <= F(n+1) <= 2^31` (the precondition's bound) — `qpow_bounded` +
   `fib_mono` + `entries_bounded` transport that across `view` to the u64 fields.
3. **The top-left value.** `(Q^n).a == F(n+1)` (`qpow_topleft`), so
   `fib_matrix(n) == F(n+1)`.

## Why this would be brutal in Z3

It is Chapters 5 and 7 stacked, plus a layer of matrix algebra:

- **A custom monoid.** `mat_mul` associativity and the matrix exponent laws
  (`mat_pow_add`, `mat_pow_square`) are structural facts Z3 won't synthesize; a
  proof assistant proves the monoid laws once and *composes* them.
- **Power-at-a-doubled-index over a non-commutative structure.** The Chapter 5
  difficulty (`F` at twice the index), now for 2×2 matrices where you may *not*
  commute factors — associativity has to carry the whole argument.
- **It rests on the addition formula** (Chapter 3) routed through the matrix
  identity — composition of verified lemmas all the way down.

## Exercises

1. **Drop to the pair.** Specialize `qpow_exec`'s matrix to its first column and
   recover Chapter 7's `fast_fib` line-for-line — the "redundant entries elided"
   claim, made concrete.
2. **Lucas numbers.** `[[1,1],[1,0]]^n` also encodes the Lucas sequence via the
   trace. State and prove `L(n) = (Q^n).a + (Q^n).d`.
3. **A different recurrence.** Any constant-coefficient linear recurrence is a
   matrix power. Pick `T(n) = T(n-1) + 2·T(n-2)`, write its 2×2 companion matrix,
   and reuse `qpow_exec` (it's generic in the matrix) to get an O(log n)
   evaluator.

## What's next

This closes both the Fibonacci arc *and* the fast-algorithms arc by showing they
were one arc: induction (1) → strong induction & the addition formula (3) →
fast exponentiation (5) → fast-doubling (7) → **the matrix power that unifies
them (8)**. The remaining direction the tutorial points at is **combinatorics** —
Pascal's rule, the binomial theorem, hockey stick — the proof-fn-first thread
closer to Chapter 3.
