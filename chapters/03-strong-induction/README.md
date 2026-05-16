# Chapter 3: Strong induction

Chapter 2's proofs all had the shape "assume the property holds at `k`, prove it at `k + 1`." That's **plain induction**, and it's all you need for most recursive specs — `sum_to`, factorial, anything with single-step recursion.

But Fibonacci's recurrence is `fib(n) = fib(n - 1) + fib(n - 2)`. To prove a property of `fib(n)`, you often need the property at *both* `n - 1` and `n - 2`. Plain induction reaches only one step back. We need **strong induction**: assume the property holds at *every* smaller value, and prove it at `n`.

In this chapter we prove a Fibonacci bound — `fib(n) ≤ 2^n` — that needs strong induction. The proof shape is the same one you'd use for any two-back recurrence: Cassini's identity, the addition formula, fast-doubling, …

The full code is in [`strong_induction.rs`](strong_induction.rs). Verify:

```bash
../../../tactus/source/target-verus/release/verus strong_induction.rs
# verification results:: 5 verified, 0 errors
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
    simp [hf0]
    omega

have pow_mono : pow2 (n - 2) <= pow2 (n - 1) := by
    conv_rhs => unfold pow2
    simp [hn1z]
    have h_sub : n - 1 - 1 = n - 2 := by omega
    rw [h_sub]
    omega
```

- `pow_unfold` says `2^n = 2^(n-1) + 2^(n-1)`. We unfold `pow2` once on the LHS to get `2 * pow2(n-1)`, then `omega` knows that's the same as adding it to itself.
- `pow_mono` says `2^(n-2) ≤ 2^(n-1)`. Unfolding on the RHS gives `2 * pow2(n-2)`, which is `≥ pow2(n-2)`. The `h_sub` rewrite cleans up Nat's `n - 1 - 1` to `n - 2`.

These are inline `have` clauses — small enough that we don't want them as separate proof fns, and Tactus's current behavior is to verify each proof fn independently anyway (so cross-fn lemma reuse isn't yet ergonomic). Inlining keeps everything in one file.

### The final step

```rust
conv_lhs => unfold fib
simp [hf0, hf1]
rw [show ((↑n : Int) - 2).toNat = n - 2 from by omega]

omega
```

Unfold `fib` on the LHS, eliminate the two if-branches, fix up the `.toNat` wrapper on the second recursive call (the first one collapsed via `simp`). At this point the goal is:

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

## What about the addition formula?

The headline strong-induction Fibonacci result is the **addition formula**:

> F_{m+n+1} = F_m · F_n + F_{m+1} · F_{n+1}

It needs strong induction on `m`: the inductive step uses the IH at `m - 1` AND `m - 2` to derive the result at `m`. The structure is the same `fib_le_pow2` pattern from this chapter, but the arithmetic in the recursive case is substantially heavier — we have to combine two IH instances, reason about subscript algebra (`(m + n + 1) = (m - 1) + n + 2`, etc.), and use the Fibonacci recurrence on the LHS.

It's verifiable in current Tactus, but ~60–80 lines including all the explicit subscript rewrites. We'll come back to it in a later chapter once we've built up more tooling for that kind of bookkeeping.

The reason the addition formula matters: it's the **basis of an O(log n) Fibonacci algorithm**. Substituting `m = n + 1` gives `F_{2n+2} = F_{n+1} · F_n + F_{n+2} · F_{n+1}`, and from that you can derive the *fast doubling* formulas:

> F_{2n} = F_n · (2·F_{n+1} − F_n)
> F_{2n+1} = F_n² + F_{n+1}²

Computing `fib(n)` via fast doubling takes O(log n) multiplications instead of O(n) additions. That's the kind of optimization formal verification actually unlocks: prove the algebraic identity once, then *trust* the speedup.

## Exercises

1. **Tighten the bound.** The bound `fib(n) ≤ 2^n` is loose. Try `fib(n) ≤ 2^(n - 1)` for `n ≥ 1`. Strong induction works the same way; you'll need to handle the `n = 1` base case carefully (Lean's `pow2(0) = 1`, so this becomes `fib(1) ≤ 1`).
2. **`pow2(n) ≥ 1`.** Easy with plain induction. Try it both ways: with `induction n with | zero | succ k ih` and with the recursive-fn pattern. Compare.
3. **A Fibonacci lower bound.** Prove `fib(n) ≥ n - 1` for `n ≥ 2`. (Hint: very similar structure, but be careful with `n - 1` and `n - 2` cases for small `n`.)

## What's next

Chapter 4 (planned) returns to where Chapter 2 originally pointed: **iterative Rust algorithms matching recursive mathematical specs**. With strong induction in our toolkit and Tactus's `as nat` cast fix in place, the door is open.
