# Chapter 2.5: An alternative encoding — `int` everywhere

> **Skip-or-read?** This chapter is *optional*. It revisits Chapter 2's Fibonacci identities under a different type discipline — every spec fn takes and returns `int`, never `nat`. The math is unchanged; the proofs look slightly different. Read it if you're curious about the trade-off Tactus's encoding makes between `nat` and `int`, or if you're going to verify Rust functions that mix u-typed and mathematical-integer reasoning (Chapter 1 of this tutorial is the standard `nat` path; that's the recommended starting point).

The full code is in [`fibonacci_int.rs`](fibonacci_int.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus fibonacci_int.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## Why bother?

In Chapter 2, the proof of `sum_fib_identity` had a slightly mysterious line:

```rust
rw [show ((↑k + 1 + 1 : Int) - 2).toNat = k from by omega]
```

That `.toNat` wrapper comes from Tactus rendering Verus's `(n - 1) as nat` as `Int.toNat (n - 1)`. Inside fully-typed proof goals, those `.toNat` calls clutter the state and `omega` can't see through them, so you have to peel them off by hand.

If we declare `fib` and `sum_fib` over `int` instead of `nat`, the `(n - 1) as nat` cast goes away — `n - 1` is already an `int`, the recursive call accepts an `int`, and the proof state has no `.toNat` wrappers. That's the appeal.

## The cost

`nat` carries non-negativity in its type. `fib(n) : nat` is automatically `≥ 0`. Over `int`, we lose that. For most lemmas this doesn't matter, but **Fibonacci's recursion goes two steps back** — `fib(n) = fib(n-1) + fib(n-2)` — and many proofs need both sub-values to be non-negative. So `fib_nonneg` becomes its own lemma, and a non-trivial one because plain `induction` (one step back) doesn't reach far enough. We use **strong induction**, encoded as a self-recursive proof function.

Three small recurring costs across every proof:

1. `decreases (n + 1) as nat` on every recursive spec fn — Verus's `int` decreases needs a `nat`-valued projection. `n + 1` is positive on the recursive branches, so `(n + 1) as nat` is a fine measure.
2. `requires n >= 0` on every induction proof, plus a `| pred k _ => omega` arm to dismiss the negative case as vacuous.
3. `fib_nonneg` as a prerequisite lemma whenever you'd otherwise rely on type-level positivity.

## The spec, over `int`

```rust
spec fn fib(n: int) -> int
    decreases (n + 1) as nat
{
    if n <= 0 { 0 }
    else if n == 1 { 1 }
    else { fib(n - 1) + fib(n - 2) }
}
```

The `if n <= 0` branch (rather than `if n == 0`) is a small but important change: it captures *all* non-positive inputs as base cases, including negatives. Otherwise the body's recursion would call `fib(-1)`, `fib(-2)`, … without termination. The behavior on negatives is "returns 0", which we treat as garbage (callers shouldn't pass negatives anyway).

## `fib_nonneg`: strong induction via self-recursion

```rust
proof fn fib_nonneg(n: int)
    ensures fib(n) >= 0
    decreases (n + 1) as nat
by {
    if h : n <= 0 then (
        unfold fib
        rw [if_pos h]
    ) else if h1 : n = 1 then (
        unfold fib
        rw [if_neg (by omega : ¬(n ≤ 0))]
        rw [if_pos h1]
        omega
    ) else (
        have ih1 := fib_nonneg (n - 1)
        have ih2 := fib_nonneg (n - 2)
        unfold fib
        rw [if_neg h]
        rw [if_neg h1]
        omega
    )
}
```

This is a different shape from `induction n with | zero | succ k ih`. Instead of relying on Lean's built-in induction principle, the proof is a **function that calls itself on smaller arguments**. The `decreases (n + 1) as nat` clause is what convinces Lean the recursion terminates — at each recursive call, `(n + 1) as nat` strictly decreases.

The three branches correspond to the three branches of `fib` itself. Each picks the right branch of the unfolded `if`-cascade with `rw [if_pos …]` / `rw [if_neg …]` — the stable, `simp`-free way to step through a definition (see the [note on `simp`](../../README.md#a-note-on-simp)):

- `n ≤ 0`: `rw [if_pos h]` selects `fib(n) = 0`, so the goal `0 ≥ 0` is closed outright.
- `n = 1`: `rw [if_neg …]` drops the `n ≤ 0` branch, `rw [if_pos h1]` selects `fib(1) = 1`, and `omega` finishes `1 ≥ 0`.
- `n ≥ 2`: invoke `fib_nonneg(n - 1)` and `fib_nonneg(n - 2)` for the two IHs; the two `rw [if_neg …]` drop both base cases to expose `fib(n) = fib(n-1) + fib(n-2)`; then `omega` closes from the non-negative sub-values. (Note there's no `.toNat` to clean up — that's the whole point of the `int` encoding.)

Self-recursive proofs are how strong induction is usually expressed in Lean. The "induction hypothesis at any smaller value" is just "you can call yourself."

### Surface-syntax quirk: the parentheses

You may have noticed each branch of the `if … then … else …` is wrapped in `( … )`. That's because the branches contain multiple tactics, and Lean's tactic-mode `if then else` would otherwise parse only the first tactic per branch. The parens group the multi-tactic block. (Verus's own `if let h : P then … else …` syntax — see the `rec_trivial` example in tactus's test suite — handles this with indentation; in a `by { }` block, the parens are the reliable form.)

## `sum_fib_identity` over `int`

```rust
proof fn sum_fib_identity(n: int)
    requires n >= 0
    ensures sum_fib(n) + 1 == fib(n + 1)
by {
    induction n with
    | zero => unfold sum_fib; unfold fib; decide
    | succ k ih =>
        unfold sum_fib
        rw [if_neg (by omega : ¬(↑k + 1 ≤ (0 : Int)))]
        rw [show ((↑k + 1 : Int) - 1) = ↑k from by omega]
        conv_rhs => unfold fib
        rw [if_neg (by omega : ¬(↑k + 1 + 1 ≤ (0 : Int)))]
        rw [if_neg (by omega : (↑k + 1 + 1 : Int) ≠ 1)]
        rw [show ((↑k + 1 + 1 : Int) - 1) = ↑k + 1 from by omega]
        rw [show ((↑k + 1 + 1 : Int) - 2) = ↑k from by omega]
        omega
    | pred k _ => omega
}
```

Two differences from Chapter 2's version:

1. **A `pred k _` case.** Lean's `induction` on an `Int` parameter produces three subcases: `zero`, `succ` (positive direction), `pred` (negative direction). The `requires n >= 0` makes the `pred` case vacuous — `omega` notices the contradiction and closes the goal.
2. **The rewrites are pure `Int`.** The `succ` case still steps through both definitions with `rw [if_neg …]` (dropping the `n ≤ 0` and `n == 1` base cases) and `rw [show … from by omega]` (simplifying the recursive-call indices) — the same `simp`-free machinery as Chapter 2. The difference: every `show` target here is plain `Int` arithmetic like `(↑k + 1 + 1) - 2 = ↑k`, with **no `.toNat` wrapper**. Chapter 2's `nat` version had to collapse `.toNat` shapes (via the `TactusTutorialHelpers` `simp only` lemmas); here there's nothing to collapse, so no helper import is needed — but it costs a couple of extra `rw [show …]` lines that `simp only` folded into one call there.

## Side-by-side comparison

| Aspect | Chapter 2 (`nat`) | Chapter 2.5 (`int`) |
|---|---|---|
| Spec fn signature | `fib(n: nat) -> nat` | `fib(n: int) -> int` |
| `decreases` | `n` | `(n + 1) as nat` |
| Base case for fib | `if n == 0` (forbid negatives by type) | `if n <= 0` (define as 0 on negatives) |
| Proof fn signature | `(n: nat)` | `(n: int) requires n >= 0` |
| Induction cases | `zero`, `succ` | `zero`, `succ`, `pred` |
| Non-negativity | free (from type) | needs `fib_nonneg` lemma |
| `fib_nonneg` proof | not needed | self-recursive (strong induction) |
| `.toNat` in goals | yes — one `rw` per nontrivial proof | no |
| Lines of proof | ~30 for both lemmas | ~35 (fib_nonneg adds ~10, sum_fib_identity loses 1) |

The two encodings are roughly equivalent in proof complexity for Fibonacci specifically. For lemmas with *one-step* recursion (like factorial), `int` would win — `fib_nonneg`-style positivity proofs are easier with plain induction.

## When you'd actually use this encoding

The `int` encoding shines when you're mixing **mathematical specs** with **u-typed exec functions**. Tactus renders `u64` etc. as Lean `Int`, so a spec fn over `int` accepts `u64` arguments without a coercion at the call site — meaning loop invariants and postconditions like `result == fib(i)` (where `i : u64`) elaborate cleanly. The `nat` encoding requires `fib(i as nat)` which lowers as `fib (Int.toNat i)`, and that extra wrapper trips up automation downstream.

If you ever return to the "iterative Rust function matches recursive math spec" pattern (originally planned as Chapter 2 with `factorial`), the `int` encoding is the path of least resistance.

## What's next

Chapter 3 returns to Chapter 2's `nat` encoding and tackles the **Fibonacci addition formula**:

> F_{m+n+1} = F_m · F_n + F_{m+1} · F_{n+1}

Strong induction makes a second appearance — this time over two variables — and the result opens the door to an O(log n) Fibonacci algorithm.
