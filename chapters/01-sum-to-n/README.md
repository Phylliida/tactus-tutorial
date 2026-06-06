# Chapter 1: Sum to n

> **Claim.** For every natural number n, 1 + 2 + … + n = n(n+1)/2.

You almost certainly already believe this. The point of this chapter isn't the result — it's seeing how Tactus lets us *state* the claim in Rust and *prove* it in Lean, in about ten lines.

The full code is in [`sum_to_n.rs`](sum_to_n.rs). To verify it:

```bash
../../../tactus/source/target-verus/release/verus --lean-backend sum_to_n.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
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
    | zero => unfold sum_to; decide
    | succ k ih =>
        unfold sum_to
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]
        nlinarith [ih]
}
```

The `by { ... }` block is **Lean tactic syntax**, passed through Tactus verbatim. Let's read it:

1. **`induction n`** does case analysis on the natural number `n`. Lean's natural numbers are defined as either `zero` or `succ k` (where `k` is itself a natural). Each `|` arm handles one of those cases.

2. **`zero` case** — the goal is `2 * sum_to(0) == 0 * (0 + 1)`, i.e., `0 == 0`. `unfold sum_to` exposes the body of the definition (so Lean knows `sum_to(0) = 0`), and `decide` settles the concrete arithmetic.

3. **`succ k ih` case** — `k : Nat` is the predecessor, and `ih : 2 * sum_to(k) == k * (k + 1)` is the **induction hypothesis** automatically brought into scope. The goal becomes `2 * sum_to(k+1) == (k+1) * (k+2)`. Three steps clear it:
   - `unfold sum_to` exposes the body, leaving `2 * (if k + 1 == 0 then 0 else (k + 1) + sum_to(…)) == …`.
   - `rw [if_neg …]` discharges the `if` — the condition `k + 1 = 0` is false. We use `if_neg`, a stable core lemma, rather than a bare `simp`: `simp`'s behavior is governed by Mathlib's evolving `@[simp]` set, so leaning on it for an *intermediate* step makes the proof fragile across Mathlib updates (see the [note on `simp`](../../README.md#a-note-on-simp)).
   - `rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]` cleans up a cast wrapper. Tactus renders the spec's `(n - 1) as nat` as `Int.toNat (↑n - 1)`; this rewrite collapses `((k+1) - 1).toNat` back to `k`, so the recursive call reads as `sum_to(k)` and matches `ih`. (You'll meet this `.toNat` wrinkle properly in Chapter 2 — here it's just one line.)
   - `nlinarith [ih]` finishes the polynomial identity `2 * (k + 1 + sum_to k) == (k + 1) * (k + 2)`, using `ih` as a fact.

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

## From spec to implementation: verifying an iterative `sum_iter`

Now the headline Tactus use case. We've proved `2·sum_to(n) = n·(n+1)`. Suppose we write an iterative Rust function that's *supposed* to compute the same thing. Can we verify it against the math?

```rust
#[verifier::tactus_auto]
#[verifier::tactus_tactic("first | tactus_auto | (intros; nlinarith)")]
fn sum_iter(n: u64) -> (r: u64)
    requires n <= 1000
    ensures 2 * r == n * (n + 1)
{
    let mut result: u64 = 0;
    let mut i: u64 = 0;
    while i < n
        invariant
            i <= n,
            n <= 1000,
            2 * result == i * (i + 1),
            result <= 1001 * 1001,
        decreases n - i
    {
        i = i + 1;
        result = result + i;
    }
    result
}
```

Three pieces to read:

- **`#[verifier::tactus_auto]`** tells Tactus to auto-generate verification conditions for this exec fn (loop invariants, overflow checks, postcondition). Without it, Tactus would treat the body as opaque.
- **The `invariant` clauses** are what the verifier checks holds at every loop iteration — *and* what's available as hypotheses when discharging the postcondition. The key one is `2 * result == i * (i + 1)`, the closed form we already know is correct from `sum_formula`.
- **`decreases n - i`** is the termination measure. The loop body must strictly decrease it; here `i = i + 1` does.

### What the verifier asks for

Tactus emits one Lean theorem per obligation. For this fn:

1. **Loop invariant init** — at entry (`result = 0, i = 0`): does `2·0 = 0·1`? Yes, `omega` closes.
2. **Loop invariant maintain** — given the invariant holds with `(i, result)`, does it hold with `(i + 1, result + (i + 1))`? Need to show `2·(result + (i + 1)) = (i + 1)·(i + 2)`. From the old invariant `2·result = i·(i + 1)`, this is a polynomial identity: `2·result + 2·(i + 1) = i·(i + 1) + 2·(i + 1) = (i + 1)·(i + 2)`. `nlinarith` solves it.
3. **Overflow check** — `result + (i + 1) < 2⁶⁴`. The bound `result <= 1001 * 1001` plus `i <= n <= 1000` makes this trivial for omega.
4. **Postcondition** — at exit (`i == n` from `i <= n` + `¬(i < n)`): substitute `i := n` in the invariant to get `2·r = n·(n + 1)`. omega does the substitution.

### The `tactus_tactic` line

The default closer is `rfl | decide | omega | simp_all | tactus_case_split | fail`. None of those handles nonlinear arithmetic — `omega` is linear-only, `simp_all` doesn't know polynomial identities. So the maintain step (item 2) would fail.

The `tactus_tactic` attribute lets us extend the closer:

```rust
#[verifier::tactus_tactic("first | tactus_auto | (intros; nlinarith)")]
```

This says "try the default `tactus_auto` first; if it fails, introduce the hypotheses and try `nlinarith`." `intros; nlinarith` is the magic incantation for nonlinear obligations: `intros` brings the local context (loop variables, invariants) into scope, then `nlinarith` (from `Mathlib.Tactic.Linarith`) discharges polynomial identities.

### Why this is the moment Tactus delivers

We just used a recursive *mathematical* definition (`sum_to`), proved a closed-form identity about it (`sum_formula`), and then verified that an *iterative Rust function* satisfies that identity. The Rust code can be compiled and run; the verification guarantees it computes the right value for any input up to the precondition's bound.

A pure runtime test would tell you the function happens to be right on the inputs you tested. The verification tells you it's right on *every* input — and any future refactor that breaks the math will fail to verify before it can ship.

## Exercises

1. **Odd-number identity.** Prove `1 + 3 + 5 + … + (2n − 1) = n²` by defining `sum_odd(n: nat)` recursively and following the same `induction` shape as `sum_formula`. The base case is `sum_odd(0) == 0`; the inductive step uses `sum_odd(k + 1) = sum_odd(k) + (2k + 1)`.

2. **Iterative `sum_odd_iter`.** Write a loop that accumulates the odd-number sum and verify it against `r == n * n`. The structure mirrors `sum_iter` but with a different invariant.

3. **Tighten the precondition.** `sum_iter` requires `n <= 1000`. What's the largest `n` for which `2 * n * (n + 1)` fits in `u64`? Bump the precondition to that bound and see if the verifier still closes (you may need to adjust the `result <= …` invariant accordingly).

## What's next

Chapter 2 turns to Fibonacci identities — same `induction` machinery, but with two base cases and an extra `rw` for handling Tactus's `.toNat` wrappers. It's the warm-up for strong induction in Chapter 3.
