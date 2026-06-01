# Chapter 3: Strong induction

Chapter 2's proofs all had the shape "assume the property holds at `k`, prove it at `k + 1`." That's **plain induction**, and it's all you need for most recursive specs — `sum_to`, factorial, anything with single-step recursion.

But Fibonacci's recurrence is `fib(n) = fib(n - 1) + fib(n - 2)`. To prove a property of `fib(n)`, you often need the property at *both* `n - 1` and `n - 2`. Plain induction reaches only one step back. We need **strong induction**: assume the property holds at *every* smaller value, and prove it at `n`.

In this chapter we prove a Fibonacci bound — `fib(n) ≤ 2^n` — that needs strong induction. The proof shape is the same one you'd use for any two-back recurrence: Cassini's identity, the addition formula, fast-doubling, …

The full code is in [`strong_induction.rs`](strong_induction.rs). Verify:

```bash
../../../tactus/source/target-verus/release/verus strong_induction.rs
# verification results:: 7 verified, 0 errors
```

## The encoding

Lean's built-in `induction n with | zero | succ k ih` gives you `ih : P k` — one step back. Strong induction needs `ih : ∀ m, m < n → P m` — at any smaller value.

The cleanest way to express that in Lean (and Tactus) is **as a recursive proof function**: the proof of `P n` is itself a function that *calls itself* on smaller inputs. The recursive calls play the role of the induction hypothesis "at any smaller value."

```rust
proof fn fib_le_pow2(n: nat)
    ensures fib(n) <= pow2(n)
    decreases n
by {
    if h0 : n = 0 then ( /* base case */ )
    else if h1 : n = 1 then ( /* second base case */ )
    else (
        have ih1 := fib_le_pow2 (n - 1)
        have ih2 := fib_le_pow2 (n - 2)
        // … combine ih1 and ih2 to prove the goal at `n` …
    )
}
```

Three structural ideas:

- **`decreases n`** is what Lean uses to verify the recursion terminates. At each recursive call, the measure must strictly decrease. Here `n - 1 < n` and `n - 2 < n` both hold (in the recursive case, where `n ≥ 2`), so termination is automatic.
- **Two base cases.** Plain induction has one base case (`zero`). Strong induction often has *as many base cases as the recursion has steps back* — for two-back, you need both `n = 0` and `n = 1` handled before the recursive case.
- **The recursive calls (`fib_le_pow2 (n - 1)`, `fib_le_pow2 (n - 2)`) are syntactically the same as calling any function.** That's the whole point: there's no special "strong induction" tactic, just a function that calls itself on smaller inputs.

## The bound and its proof

We prove `fib(n) ≤ 2^n`. It's loose (Fibonacci grows like φⁿ ≈ 1.618ⁿ, much slower than 2ⁿ) but easy to state in Verus and natural for strong induction.

```rust
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
```

The proof is the recursive-fn shape above. Let's read the inductive case.

### Setting up the IH

```rust
have ih1 := fib_le_pow2 (n - 1)   // ih1 : fib(n - 1) ≤ pow2(n - 1)
have ih2 := fib_le_pow2 (n - 2)   // ih2 : fib(n - 2) ≤ pow2(n - 2)
```

Two recursive calls give us the bound at both predecessors.

### Two helper facts about `pow2`

The recursive case combines `ih1`, `ih2`, and two facts about `pow2`:

```rust
have pow_unfold : pow2 n = pow2 (n - 1) + pow2 (n - 1) := by
    conv_lhs => unfold pow2
    rw [if_neg hf0]
    rw [show ((↑n : Int) - 1).toNat = n - 1 from by omega]
    omega

have pow_mono : pow2 (n - 2) <= pow2 (n - 1) := by
    conv_rhs => unfold pow2
    rw [if_neg hn1z]
    rw [show ((↑(n - 1) : Int) - 1).toNat = n - 2 from by omega]
    omega
```

Both follow the same `simp`-free shape from chapters 1–2 — unfold the definition, drop the base-case `if` with `rw [if_neg …]`, then collapse the `.toNat` cast on the recursive index with `rw [show … from by omega]`:

- `pow_unfold` says `2^n = 2^(n-1) + 2^(n-1)`. Unfolding `pow2` on the LHS and dropping the `n == 0` branch (`hf0 : ¬(n = 0)`) leaves `2 * pow2(n-1)`; `omega` knows that's the same as adding it to itself.
- `pow_mono` says `2^(n-2) ≤ 2^(n-1)`. Unfolding on the RHS and dropping the `n - 1 == 0` branch (`hn1z`) gives `2 * pow2(n-2)`, which is `≥ pow2(n-2)`. The `rw [show …]` turns the recursive index `(↑(n-1) - 1).toNat` into `n - 2` so the two sides line up for `omega`.

These are inline `have` clauses — small enough that we don't want them as separate proof fns, and Tactus's current behavior is to verify each proof fn independently anyway (so cross-fn lemma reuse isn't yet ergonomic). Inlining keeps everything in one file.

### The final step

```rust
conv_lhs => unfold fib
rw [if_neg hf0]
rw [if_neg hf1]
rw [show ((↑n : Int) - 1).toNat = n - 1 from by omega]
rw [show ((↑n : Int) - 2).toNat = n - 2 from by omega]
omega
```

Unfold `fib` on the LHS, drop its two base cases with `rw [if_neg …]`, then collapse the `.toNat` wrappers on *both* recursive calls (`(↑n - 1).toNat → n - 1` and `(↑n - 2).toNat → n - 2`). At this point the goal is:

```
fib(n - 1) + fib(n - 2) <= pow2 n
```

with `ih1`, `ih2`, `pow_unfold`, and `pow_mono` all in scope. `omega` chains them: `fib(n-1) + fib(n-2) ≤ pow2(n-1) + pow2(n-2) ≤ pow2(n-1) + pow2(n-1) = pow2(n)`.

## Why this would be painful in Z3

Strong induction is *exactly* the proof structure Z3 doesn't have. To prove `fib(n) ≤ 2^n` over Z3, you'd typically:

- Hand-write a helper proof function with the same recursive shape as `fib`.
- Inside each recursive call site, supply explicit `fuel` annotations telling Z3 how many times to unroll `fib`.
- Manually provide both `ih1` and `ih2` as ladder lemmas.
- Burn rlimit on the heuristic search that follows.

A typical Verus proof of a Fibonacci bound is 30–60 lines of careful scaffolding. Lean's `decreases`-driven recursion turns that into "call yourself on smaller arguments; Lean checks termination."

## The headline result: the addition formula

The classical strong-induction Fibonacci identity is the **addition formula**:

> F_{m+n+1} = F_m · F_n + F_{m+1} · F_{n+1}

Its proof has the same shape as `fib_le_pow2` — two base cases plus a recursive case that uses the IH at both `m - 1` and `m - 2` — but the algebra at the end is heavier: we combine *two* IH instances with the Fibonacci recurrence applied at *three* positions. The full proof is in [`strong_induction.rs`](strong_induction.rs); here we walk through the recursive case.

### Setup

```rust
have ih1 := fib_addition (m - 1) n
have ih2 := fib_addition (m - 2) n
```

The IHs come out with subscripts like `(m - 1) + n + 1`, which we'd like in the form `m + n`. Omega handles all of these:

```rust
have e1a : (m - 1) + n + 1 = m + n := by omega
have e1b : (m - 1) + 1 = m := by omega
rw [e1a, e1b] at ih1
```

After the rewrites:

```
ih1 : fib (m + n)     = fib (m - 1) · fib n + fib m       · fib (n + 1)
ih2 : fib (m + n - 1) = fib (m - 2) · fib n + fib (m - 1) · fib (n + 1)
```

### Three uses of the Fibonacci recurrence

Each follows the same pattern from chapter 2: unfold `fib` once, simplify the if-cascade, fix up the `.toNat` wrapper.

```rust
have step_m    : fib m         = fib (m - 1) + fib (m - 2)        := by ...
have step_m1   : fib (m + 1)   = fib m + fib (m - 1)              := by ...
have step_sum  : fib (m + n + 1) = fib (m + n) + fib (m + n - 1)  := by ...
```

### Combining

```rust
nlinarith [step_sum, ih1, ih2, step_m, step_m1]
```

`nlinarith` is `linarith` with multiplication — it solves polynomial identities given a set of facts. Reading the algebra by hand:

```
F_{m+n+1}
  = F_{m+n} + F_{m+n-1}                                          [step_sum]
  = (F_{m-1} F_n + F_m F_{n+1}) + (F_{m-2} F_n + F_{m-1} F_{n+1}) [ih1, ih2]
  = (F_{m-1} + F_{m-2}) F_n + (F_m + F_{m-1}) F_{n+1}             [factor]
  = F_m F_n + F_{m+1} F_{n+1}                                    [step_m, step_m1]
```

`nlinarith` finds this chain automatically from the five facts in scope.

### Why this is worth the trouble

Substituting `m = n` into the addition formula collapses it to:

> F_{2n+1} = F_n² + F_{n+1}²

And a similar substitution gives:

> F_{2n} = F_n · (2·F_{n+1} − F_n)

These are the **fast-doubling** formulas. They let you compute `F_n` in O(log n) multiplications instead of O(n) additions — exponentially faster than the naive recurrence. Once the addition formula is proved, an iterative Rust function that does fast doubling can be verified against `fib` with the addition formula as its key lemma. That's the kind of "prove once, optimize freely" payoff formal verification delivers.

## Exercises

1. **Tighten the bound.** The bound `fib(n) ≤ 2^n` is loose. Try `fib(n) ≤ 2^(n - 1)` for `n ≥ 1`. Strong induction works the same way; you'll need to handle the `n = 1` base case carefully (Lean's `pow2(0) = 1`, so this becomes `fib(1) ≤ 1`).
2. **`pow2(n) ≥ 1`.** Easy with plain induction. Try it both ways: with `induction n with | zero | succ k ih` and with the recursive-fn pattern. Compare.
3. **A Fibonacci lower bound.** Prove `fib(n) ≥ n - 1` for `n ≥ 2`. (Hint: very similar structure, but be careful with `n - 1` and `n - 2` cases for small `n`.)

## What's next

Chapter 4 returns to where Chapter 2 originally pointed: **iterative Rust algorithms matching recursive mathematical specs**. With strong induction in our toolkit and Tactus's `as nat` cast fix in place, the door is open — we verify an iterative `factorial` against the recursive `fact` spec.
