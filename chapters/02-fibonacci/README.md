# Chapter 2: Fibonacci identities

Chapter 1 proved a closed-form identity about `sum_to` with a single `induction` tactic. The proof was beautiful precisely because the spec was *one-step*: one base case, one recursive call.

Fibonacci is the natural next step. The definition has **two base cases** and **two recursive calls**, and the classical identities about it are a workout for any proof system. We'll prove two of them here:

> 1. **Positivity.** F_n ≥ 1 for all n ≥ 1.
> 2. **Sum identity.** F_0 + F_1 + … + F_n = F_{n+1} − 1.

The full code is in [`fibonacci.rs`](fibonacci.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus fibonacci.rs
# verification results:: 9 verified, 0 errors
```

## Defining `fib`

```rust
spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}
```

Two things changed since chapter 1's `sum_to`:

- **Two base cases** (`n == 0` and `n == 1`) handled in a nested `if`. We can't combine them — `fib(1)` is defined directly, not in terms of any smaller `fib`.
- **Two recursive calls.** Tactus emits a `decreases n` termination measure; both `(n-1)` and `(n-2)` are strictly less than `n` when `n ≥ 2`, so Lean accepts it.

## Concrete check: `fib(7) = 13`

A useful sanity check. The proof is one line, but it's not a one-step `unfold`:

```rust
proof fn fib_seven()
    ensures fib(7) == 13
by {
    repeat (unfold fib; simp)
}
```

`repeat (unfold fib; simp)` keeps unfolding `fib` and simplifying until every `fib` call has reduced to a literal. For `fib(7)` that takes about eight iterations — Lean does it transparently.

## Lemma 1: `fib(n) ≥ 1` for `n ≥ 1`

A warm-up. The trickiness is that the inductive step needs to handle two cases:

- When the predecessor `k = 0`, we're proving `fib(1) ≥ 1`, which is `1 ≥ 1`.
- When `k > 0`, the induction hypothesis tells us `fib(k) ≥ 1`, and the recurrence `fib(k+1) = fib(k) + fib(k-1)` gives the rest.

```rust
proof fn fib_pos(n: nat)
    requires n >= 1
    ensures fib(n) >= 1
    decreases n
by {
    induction n with
    | zero => omega
    | succ k ih =>
        unfold fib
        by_cases h : k = 0
        · subst h; simp
        · simp [h]
          have hk : k >= 1 := by omega
          have ihk := ih hk
          omega
}
```

A few things worth noticing:

- **`induction n`** is the same tactic from chapter 1. The `zero` case is vacuous here because the `requires n >= 1` hypothesis contradicts `n = 0` — `omega` spots that and closes the goal.
- **`by_cases h : k = 0`** introduces a case split on whether `k` is zero. The two `·` bullets handle each branch.
- **`simp [h]`** uses the hypothesis `h : ¬(k = 0)` to simplify the inner `if k = 0` away.
- **`have ihk := ih hk`** instantiates the induction hypothesis. `ih` has type `k ≥ 1 → fib k ≥ 1`; supplying `hk : k ≥ 1` gives us `ihk : fib k ≥ 1`. Now `omega` can close the arithmetic.

This kind of bookkeeping — case-split, instantiate IH, run omega — is the rhythm of most Fibonacci proofs.

## Lemma 2: the sum identity

The classical statement is `F_0 + F_1 + … + F_n = F_{n+1} − 1`. Subtracting 1 from a `nat` is awkward, so we rephrase:

> **sum_fib(n) + 1 = F_{n+1}**

where `sum_fib(n)` is `F_0 + F_1 + … + F_{n-1}`. The definition is the obvious recursion:

```rust
spec fn sum_fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else { fib((n - 1) as nat) + sum_fib((n - 1) as nat) }
}
```

And the proof:

```rust
proof fn sum_fib_identity(n: nat)
    ensures sum_fib(n) + 1 == fib(n + 1)
by {
    induction n with
    | zero => unfold sum_fib; unfold fib; decide
    | succ k ih =>
        unfold sum_fib
        simp
        conv_rhs => unfold fib
        simp
        rw [show ((↑k + 1 + 1 : Int) - 2).toNat = k from by omega]
        omega
}
```

Let's read the inductive step. After `unfold sum_fib; simp`, the goal looks like:

```
fib k + sum_fib k + 1 = fib (k + 1 + 1)
```

We unfold `fib` on the **right-hand side only** (via `conv_rhs => unfold fib`), exposing the recurrence:

```
fib k + sum_fib k + 1 = fib (k + 1) + fib ((↑k + 1 + 1 - 2).toNat)
```

Two arithmetic noisy bits remain:

1. `fib (k + 1)` — this matches `ih`'s right side, so we'll feed both into `omega`.
2. `fib ((↑k + 1 + 1 - 2).toNat)` — should be `fib k`, but the `.toNat` wrapper hides it.

The `rw [show ((↑k + 1 + 1 : Int) - 2).toNat = k from by omega]` rewrite says: "*establish the equation* `(↑k + 1 + 1 - 2).toNat = k` *using omega, then rewrite with it*." That collapses the second term to `fib k`. With both sides now in terms of `fib k`, `fib (k+1)`, and `sum_fib k`, `omega` closes using the induction hypothesis.

### Where does `.toNat` come from?

It's how Tactus lowers Verus's `(n - 1) as nat` cast. In Verus, `n - 1` for a `nat` is widened to `int` (so it can go negative), and the `as nat` cast brings it back to `nat`, saturating at 0 if it was negative. The Lean rendering is faithful to this: `Int.toNat`. Inside a fully-typed proof state, the wrappers add visual noise; `omega` reasons through them when the goal is pure arithmetic, but not when they're nested inside a function call like `fib (...).toNat`. The little `rw` is the bridge.

You'll see this pattern often. The good news: it's always the same shape — `rw [show <messy_expr> = <clean_expr> from by omega]`.

## Why this would be painful in Z3

Both proofs use **induction**, the structural feature Lean has and Z3 does not. The sum identity also needs Lean's **rewriting machinery**: the ability to manipulate the goal under a recursive definition, expose the recurrence, and combine it with an arithmetic hypothesis. In a Z3 setting you'd either write a hand-rolled recursive helper proof (often longer than the spec itself) or burn rlimit on heuristic search that may or may not converge.

## Exercises

1. **Prove `fib(n) <= fib(n+1)`** — Fibonacci is non-decreasing. Direct `induction`, no rewrites needed for the most part.
2. **Compute `fib(10)`** — should be 55. One line.
3. **Define `even_indexed_sum(n)`** as F_0 + F_2 + F_4 + … + F_{2n} and prove it equals F_{2n+1}. This needs careful subscript handling; you'll write a few more `rw` lines.

## What's next

Chapter 3 will introduce **strong induction** via the Fibonacci addition formula:

> F_{m+n+1} = F_m · F_n + F_{m+1} · F_{n+1}

This identity is the door to an O(log n) Fibonacci algorithm — and the proof reaches *two* levels back, which plain `induction` can't do.
