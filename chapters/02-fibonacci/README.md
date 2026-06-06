# Chapter 2: Fibonacci identities

Chapter 1 proved a closed-form identity about `sum_to` with a single `induction` tactic. The proof was beautiful precisely because the spec was *one-step*: one base case, one recursive call.

Fibonacci is the natural next step. The definition has **two base cases** and **two recursive calls**, and the classical identities about it are a workout for any proof system. We'll prove two of them here:

> 1. **Positivity.** F_n ≥ 1 for all n ≥ 1.
> 2. **Sum identity.** F_0 + F_1 + … + F_n = F_{n+1} − 1.

The full code is in [`fibonacci.rs`](fibonacci.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus --lean-backend fibonacci.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
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

A useful sanity check — and the first place the `simp`-robustness rule bites. The proof unfolds `fib` once per recursion level, then closes with a single `simp`:

```rust
proof fn fib_seven()
    ensures fib(7) == 13
by {
    unfold fib
    unfold fib
    unfold fib
    unfold fib
    unfold fib
    unfold fib
    unfold fib
    unfold fib
    simp
}
```

Eight explicit `unfold fib`s walk the recursion down to the base cases, and the closing `simp` evaluates the resulting `if`-cascade to the literal `13`. A *closing* `simp` is fine — if it doesn't finish, the proof just fails, the same failure mode as any other closer.

You might expect `repeat (unfold fib; simp)` to do this in one line. It has two problems. The `simp` would now be an *intermediate* step (the `repeat` runs it between unfolds), which the [note on `simp`](../../README.md#a-note-on-simp) warns against. And — worse for `fib` specifically — `repeat unfold fib` keeps unfolding the `fib` calls sitting in the *dead* `else`-branches of already-decided base cases (`if 0 == 0 then 0 else fib(…) + fib(…)`), so the term blows up exponentially; for `fib(10)` it exhausts Lean's heartbeat budget. The fixed-length unfold list stops before that and lets `simp` prune the dead branches. (Chapter 4's `fact` proof *can* use `repeat unfold fact`, because `fact` has a single recursive call and no dead branches to over-expand.)

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
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        by_cases h : k = 0
        · subst h
          rw [if_pos (by decide : (0 + 1 : Nat) = 1)]
        · rw [if_neg (by omega : (k + 1 : Nat) ≠ 1)]
          rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]
          have hk : k >= 1 := by omega
          have ihk := ih hk
          omega
}
```

A few things worth noticing:

- **`induction n`** is the same tactic from chapter 1. The `zero` case is vacuous here because the `requires n >= 1` hypothesis contradicts `n = 0` — `omega` spots that and closes the goal.
- **`unfold fib` then `rw [if_neg …]`** exposes `fib(k+1)`'s body and drops its first base case (`k + 1 = 0` is false). As in chapter 1, we use `rw [if_neg …]` rather than `simp` so the step doesn't depend on Mathlib's evolving `@[simp]` set.
- **`by_cases h : k = 0`** splits on whether `k` is zero; the two `·` bullets handle each branch:
  - When `k = 0`: `subst h` rewrites, and the second base case fires — `rw [if_pos …]` picks the `n == 1` branch, leaving `fib(1) = 1 ≥ 1`.
  - When `k ≠ 0`: `rw [if_neg …]` drops the second base case too, then `rw [show … toNat …]` collapses the cast on the recursive call so it reads as `fib k`.
- **`have ihk := ih hk`** instantiates the induction hypothesis. `ih` has type `k ≥ 1 → fib k ≥ 1`; supplying `hk : k ≥ 1` gives `ihk : fib k ≥ 1`. Now `omega` closes the arithmetic, since `fib(k+1) = fib(k) + fib(k-1) ≥ fib(k) ≥ 1`.

This rhythm — drop the base-case `if`s, fix the `.toNat` on each recursive call, instantiate the IH, run `omega` — is the shape of most Fibonacci proofs.

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
        rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
        conv_rhs => unfold fib
        rw [if_neg (by omega : (k + 1 + 1 : Nat) ≠ 0)]
        rw [if_neg (by omega : (k + 1 + 1 : Nat) ≠ 1)]
        simp only [TactusTut.toNat_succ_sub_one,
                   TactusTut.toNat_succ_succ_sub_one,
                   TactusTut.toNat_succ_succ_sub_two]
        omega
}
```

This proof leans on `import TactusTutorialHelpers` (at the top of the file) — a handful of pinned `@[simp]` lemmas for the `.toNat` shapes; [Chapter 0](../00-setup/README.md#step-45-install-the-tutorials-helper-lemmas) covers installing it. Let's read the inductive step:

- **`unfold sum_fib` then `rw [if_neg …]`** exposes `sum_fib(k+1)`'s body and drops its base case (`k + 1 = 0` is false). The left side is now `fib ((↑(k+1) - 1).toNat) + sum_fib ((↑(k+1) - 1).toNat) + 1` — `.toNat` casts still attached.
- **`conv_rhs => unfold fib`** unfolds `fib` on the **right-hand side only**, and the two `rw [if_neg …]` drop *its* two base cases (`k + 1 + 1` is neither `0` nor `1`), exposing the recurrence `fib ((↑(k+1+1) - 1).toNat) + fib ((↑(k+1+1) - 2).toNat)`.
- **`simp only [TactusTut.toNat_succ_sub_one, …]`** collapses all three `.toNat` shapes at once, using the pinned helper lemmas: the goal becomes `fib k + sum_fib k + 1 = fib (k + 1) + fib k`. `simp only` with an *explicit* lemma list is stable — it never consults Mathlib's evolving default `@[simp]` set, so it's exempt from the [intermediate-`simp` caution](../../README.md#a-note-on-simp).
- **`omega`** closes using the induction hypothesis `ih : sum_fib k + 1 = fib (k + 1)`.

### Where does `.toNat` come from?

It's how Tactus lowers Verus's `(n - 1) as nat` cast. In Verus, `n - 1` for a `nat` is widened to `int` (so it can go negative), and the `as nat` cast brings it back to `nat`, saturating at 0 if it was negative. The Lean rendering is faithful to this: `Int.toNat`. Inside a fully-typed proof state, the wrappers add visual noise; `omega` reasons through them when the goal is pure arithmetic, but not when they're nested inside a function call like `fib ((…).toNat)`. Collapsing them is the recurring chore. Two equivalent bridges show up across the tutorial: an inline `rw [show <messy> = <clean> from by omega]` (used in `fib_pos` above and throughout Chapter 3), or — for the handful of *unconditional* shapes — the pinned `@[simp]` lemmas in `TactusTutorialHelpers` fired via `simp only [...]`, as here.

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
