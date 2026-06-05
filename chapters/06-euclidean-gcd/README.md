# Chapter 6: Euclidean gcd

> **Claim.** The iterative Rust function `gcd_iter(a, b)` computes the greatest
> common divisor of `a` and `b`, and matches the recursive definition `gcd` —
> for every pair of `u64`s. No overflow precondition needed.

After Chapter 5's fast-exponentiation capstone, this chapter is a palate
cleanser that introduces one genuinely new ingredient: **modular arithmetic**,
including in the termination argument. It's also the chapter where the gap
between the recursive spec and the iterative implementation is the *smallest* in
the whole tutorial — because, as you'll see, the spec **is** the loop step.

The full code is in [`gcd.rs`](gcd.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus gcd.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## The specification

```rust
spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd(b, (a % b) as nat) }
}
```

This is Euclid's algorithm, stated as a recurrence: `gcd(a, 0) = a`, and
otherwise `gcd(a, b) = gcd(b, a mod b)`. The second argument strictly shrinks
each call (`a % b < b`), which is why `decreases b` is the right termination
measure.

> **A termination subtlety.** `a % b < b` is true exactly when `b ≠ 0` — and the
> recursive call is in the `else` branch, where `b ≠ 0` holds. But proving it
> needs `Nat.mod_lt`, *not* `omega`: Lean's `omega` only reasons about `%` by a
> **literal** divisor, and here the divisor `b` is a variable. (Surfacing this
> is what made writing the chapter interesting — see "Why this would be painful
> in Z3" and the project handoff notes.)

## Why this is the simplest iterative-vs-recursive chapter

Compare the three exec chapters:

| Chapter | Spec recurrence | What the loop needs beyond the recurrence |
|---|---|---|
| 4 `factorial` | `n! = n · (n−1)!` | monotonicity + a concrete bound, for **overflow** |
| 5 `pow_iter` | `bᵉ = b · bᵉ⁻¹` | a **crux lemma** (`pow_square`) — the loop is *faster* than the spec |
| 6 `gcd_iter` | `gcd(a,b) = gcd(b, a%b)` | **nothing** — the recurrence is already the loop step |

Euclid's loop does exactly what the spec's recursion does: replace `(a, b)` with
`(b, a % b)` and repeat. So there's no clever identity to discover and no growth
to bound. The only work is the boilerplate of carrying a loop invariant across
an assignment.

## The algorithm and its invariant

```rust
let mut x: u64 = a;
let mut y: u64 = b;
while y > 0 {
    let r = x % y;
    x = y;
    y = r;
}
// x is the answer
```

The whole proof hangs on one invariant:

```rust
gcd(x as nat, y as nat) == gcd(a as nat, b as nat)
```

"The gcd of the current pair equals the gcd of the original pair." It holds at
entry (`x = a`, `y = b`, so it's `gcd(a,b) = gcd(a,b)`). At exit `y == 0`, so
`gcd(x, 0) = x` and the invariant collapses to `x == gcd(a, b)` — the
postcondition, for free.

## The loop body, verified

```rust
#[verifier::tactus_auto]
fn gcd_iter(a: u64, b: u64) -> (g: u64)
    ensures g as nat == gcd(a as nat, b as nat)
```

No custom closer, no precondition. Three asserts carry the proof:

**(1) Termination — `x % y < y`.** The new `y` is `x % y`, so `decreases y`
needs `x % y < y`. As noted above `omega` can't do variable-divisor mod, so we
hand it the core lemma directly:

```rust
assert(x % y < y) by {
    intros
    apply Int.emod_lt_of_pos <;> omega   // side goal `0 < y` from the loop condition
};
```

(`u64` renders as `Int`, hence the `Int.emod` version rather than `Nat.mod_lt`.)
With this fact in scope, the loop's decrease check closes.

**(2) Maintain — `gcd(y, x % y) == gcd(a, b)`.** This is the heart of the proof,
and it's *one unfold*:

```rust
assert(gcd(y as nat, (x % y) as nat) == gcd(a as nat, b as nat)) by {
    intros
    have hmod : ((x % y : Int)).toNat = x.toNat % y.toNat :=
        Int.toNat_emod (by omega) (by omega)
    have hunf : gcd x.toNat y.toNat = gcd y.toNat (x.toNat % y.toNat) := by
        conv_lhs => unfold gcd
        rw [if_neg (by omega : y.toNat ≠ 0)]
    rw [hmod, ← hunf]
    assumption
};
```

Read it bottom-up: `hunf` is the spec unfolded one step (dropping the `b == 0`
base case because `y ≠ 0` here), giving `gcd(x,y) = gcd(y, x%y)`. `hmod` bridges
a cast — `(x % y) as nat` arrives as *Int*-emod-then-`toNat`, while the spec's
body is *Nat* mod, and `Int.toNat_emod` says they agree for non-negative
operands. After the two rewrites the goal is exactly the loop invariant
(`gcd x y = gcd a b`), which `assumption` finds. Because we proved this for the
*old* `x`, `y` right before the assignment, the post-assignment invariant
`gcd(x, y) == gcd(a, b)` re-holds.

**(3) Exit — `x == gcd(a, b)`.** When the loop ends `y == 0`:

```rust
assert(x as nat == gcd(a as nat, b as nat)) by {
    intros
    have hy0 : y.toNat = 0 := by omega
    have hbase : gcd x.toNat (0 : Nat) = x.toNat := by unfold gcd; simp
    rw [← hbase, ← hy0]
    assumption
};
```

`hbase` is the spec's base case (`gcd(x, 0) = x`); rewriting the goal backwards
through it and `y == 0` turns `x == gcd(a, b)` into the invariant again.

## Why this would be painful in Z3

Two reasons, both familiar by now and one new:

1. **No native induction.** `gcd` is recursive, so even *stating* facts about it
   in Z3 means `reveal_with_fuel` tuning. Each unfold is a manual fuel step;
   Lean's `unfold` + `rw [if_neg …]` does one clean step.
2. **The termination measure is modular.** `a % b < b` for a *symbolic* `b` is
   exactly the kind of fact heuristic solvers handle inconsistently — it's true,
   but it's not linear, and whether the solver "sees" it depends on its mod/div
   axiomatization and triggering. Lean closes it with a named lemma
   (`Nat.mod_lt` / `Int.emod_lt_of_pos`), so termination is explicit and stable
   rather than solver-mood-dependent.

## Exercises

1. **Subtractive Euclid.** Replace the spec with the original subtraction-based
   algorithm:
   ```rust
   spec fn gcd_sub(a: nat, b: nat) -> nat
       decreases a + b
   {
       if b == 0 { a } else if a == 0 { b }
       else if a >= b { gcd_sub((a - b) as nat, b) } else { gcd_sub(a, (b - a) as nat) }
   }
   ```
   Its termination measure is `a + b` with *subtraction* obligations, which
   `omega` discharges with no `mod_lt` needed — a nice contrast with the mod
   version. Prove `gcd_sub == gcd` (induction), or just verify a subtractive
   `gcd_sub_iter` against it.
2. **gcd is positive when an input is.** Prove `a >= 1 ==> gcd(a, b) >= 1`. A
   short self-recursive proof fn (the Chapter 3 / 5 shape): the base case is
   `gcd(a, 0) = a >= 1`, and the step preserves it.
3. **Extended Euclid (Bézout).** The big one. Write `egcd(a, b) -> (g, s, t)`
   with `ensures g == gcd(a, b)` *and* `s * a + t * b == g` (over `int`, so the
   coefficients can be negative). The invariant carries two Bézout relations at
   once; it's the natural sequel and the algorithm behind modular inverses.

## What's next

The tutorial now has three worked iterative-vs-recursive proofs (factorial,
exponentiation, gcd) plus the induction and strong-induction foundations. The
remaining headline target is **fast-doubling Fibonacci** — the O(log n)
algorithm that Chapter 3's addition formula was built to unlock, and the hardest
of the bunch (two coupled identities, `F(2n)` and `F(2n+1)`, with even/odd
recursion). After that, the combinatorics thread (Pascal's rule, the binomial
theorem) opens the Sage-flavored direction.
