# Chapter 1: Sum to n

> **Claim.** For every natural number n, 1 + 2 + … + n = n(n+1)/2.

You almost certainly already believe this. The point of this chapter isn't the result — it's seeing how Tactus lets us *state* the claim in Rust and *prove* it in Lean, in about ten lines.

The full code is in [`sum_to_n.rs`](sum_to_n.rs). To verify it:

```bash
../../../tactus/source/target-verus/release/verus sum_to_n.rs
# verification results:: 8 verified, 0 errors
```

## The specification

We need a precise definition of what we're summing. We write it as a recursive `spec fn`:

```rust
spec fn sum_to(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { (n + sum_to((n - 1) as nat)) as nat }
}
```

A few things to notice:

- **`spec fn`** is a *ghost* function. It only exists at proof time — it's never compiled into a binary. Think of it as a mathematical definition you can refer to from inside specs and proofs.
- **`nat`** is the type of non-negative integers in Verus/Tactus specs. It's distinct from `u32`, `usize`, etc. — `nat` has no upper bound. (There's also `int` for the integers.)
- **`decreases n`** tells Tactus how to check that the recursion terminates. Lean refuses to accept a `def` whose termination it can't verify, and `decreases` supplies the measure.
- **`(n - 1) as nat`** is a cast. Subtraction on `nat` saturates at zero, but we've already checked `n != 0`, so the cast is well-defined.

## Restating the claim

There's one small wrinkle. We'd like to write `sum_to(n) == n * (n + 1) / 2`, but `/` on naturals is integer division — `n * (n + 1)` is always even, but Lean and Tactus would still want us to reason about the division, and that's a distraction.

The standard trick: **multiply both sides by 2**. The cleaner statement is:

```rust
proof fn sum_formula(n: nat)
    ensures 2 * sum_to(n) == n * (n + 1)
```

A `proof fn` is the Tactus equivalent of a Lean `theorem`. Its name and signature describe a claim; the body is a Lean proof. `requires` clauses become hypotheses, `ensures` clauses become the goal.

## The proof

Here it is in full:

```rust
proof fn sum_formula(n: nat)
    ensures 2 * sum_to(n) == n * (n + 1)
by {
    induction n with
    | zero => unfold sum_to; simp
    | succ k ih => unfold sum_to; simp; nlinarith [ih]
}
```

The `by { ... }` block is **Lean tactic syntax**, passed through Tactus verbatim. Let's read it:

1. **`induction n`** does case analysis on the natural number `n`. Lean's natural numbers are defined as either `zero` or `succ k` (where `k` is itself a natural). Each `|` arm handles one of those cases.

2. **`zero` case** — the goal is `2 * sum_to(0) == 0 * (0 + 1)`, i.e., `0 == 0`. `unfold sum_to` exposes the body of the definition (so Lean knows `sum_to(0) = 0`), and `simp` cleans up the arithmetic.

3. **`succ k ih` case** — `k : Nat` is the predecessor, and `ih : 2 * sum_to(k) == k * (k + 1)` is the **induction hypothesis** automatically brought into scope. The goal becomes `2 * sum_to(k+1) == (k+1) * (k+2)`.
   - `unfold sum_to; simp` rewrites `sum_to(k+1)` to `k + 1 + sum_to(k)`.
   - `nlinarith [ih]` solves the resulting polynomial identity, using `ih` as a fact.

`nlinarith` is a Mathlib tactic that handles **nonlinear arithmetic** — exactly the kind of `(k+1)(k+2)` expansion needed here. (It's why we `import Mathlib.Tactic.Linarith` at the top of the file.)

## Why is this hard for Z3?

Z3 — the solver Verus normally uses — handles linear arithmetic beautifully but has no native concept of induction. To get a proof like `2 * sum_to(n) == n * (n + 1)` past Z3, you typically have to:

- Manually write a recursive proof function with the same structure as `sum_to`.
- At each call site, supply explicit "ladder lemmas" telling Z3 how to unfold one more step of the recursion.
- Tune `reveal_with_fuel` to control how deep Z3 unrolls things.
- Sometimes write 30+ lines to get one identity to land.

Lean's `induction` tactic does all of this in one move. The kernel knows what induction *is*, so the proof is structural rather than a dance with heuristics.

## Why we needed `nlinarith`

You might wonder: if `induction` is so powerful, why does the `succ` case still need a separate tactic? Because once we've done the induction, the remaining goal is a *polynomial* identity:

> 2 · (k + 1 + sum_to k) = (k + 1) · (k + 2),  given  2 · sum_to k = k · (k + 1)

That's algebra, not induction. `nlinarith` (or `ring`, or `linear_combination`) is what finishes it. The pattern *induct, then algebra* is the most common shape of induction proof you'll see in this tutorial.

## Exercise

Add a proof of the **odd-number identity**:

> 1 + 3 + 5 + … + (2n − 1) = n²

Define `sum_odd(n: nat) -> nat` recursively, then prove:

```rust
proof fn sum_odd_is_square(n: nat)
    ensures sum_odd(n) == n * n
```

The structure is exactly like `sum_formula`. If you get stuck, the base case is `sum_odd(0) == 0`, and in the inductive step, `sum_odd(k+1) = sum_odd(k) + (2(k+1) - 1) = sum_odd(k) + 2k + 1`.

## What's next

Chapter 2 moves from "spec fns talking to themselves" to the signature Tactus use case: **a Rust function with an iterative implementation, proven equivalent to a recursive mathematical spec**. We'll start with factorial.
