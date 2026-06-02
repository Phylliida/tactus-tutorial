# Chapter 4: Iterative factorial

> **Claim.** The iterative Rust function `factorial(n)` computes `n!`, matches the recursive mathematical definition `fact`, and never overflows — for every `n ≤ 10`.

This is the chapter the whole tutorial has been building toward. Chapter 1 verified an iterative loop (`sum_iter`) against a closed-form identity; chapters 2–3 built up the induction and rewriting machinery. Here we put it together on the canonical example: a real `u64` loop verified against a **recursive** spec, with overflow safety.

The full code is in [`factorial.rs`](factorial.rs). To verify:

```bash
../../../tactus/source/target-verus/release/verus factorial.rs
# verification results:: N verified, 0 errors   (N varies by Tactus version; 0 errors is the point)
```

## The specification

```rust
spec fn fact(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}
```

Single base case (`0! = 1`), single recursive call (`n! = n · (n−1)!`). Simpler structure than Fibonacci — but the recurrence is **multiplicative**, and that one difference reshapes the whole proof compared to Chapter 1's additive `sum_iter`.

## Why this is harder than `sum_iter`

`sum_iter` had a **closed-form** invariant: `2 * result == i * (i + 1)`. That's pure polynomial arithmetic, so a single whole-function closer (`first | tactus_auto | (intros; nlinarith)`) discharged every obligation, and the loop body needed no proof annotations at all.

`factorial` has no usable closed form (Stirling's approximation isn't an equation). The honest invariant is **recurrence-based**: `result == fact(i)`. That means every loop obligation has to reason *about the spec function `fact` itself* — unfold it, relate `fact(i+1)` to `fact(i)`, bound it. A single closer tactic can't do that, because two of the obligations need to **invoke helper lemmas at specific arguments**, and a tactic string has no way to say "apply `fact_monotone` at `i+1` and `10`." So this chapter discharges its obligations with explicit `assert(P) by { … }` blocks inside the loop body. That's the general shape for recurrence-based verification; `sum_iter`'s closer-only form is the lucky special case.

## Three helper lemmas

### `fact_pos`: `n! ≥ 1`

```rust
proof fn fact_pos(n: nat)
    ensures fact(n) >= 1
    decreases n
by {
    if h : n = 0 then (
        subst h; unfold fact; decide
    ) else (
        have ih := fact_pos (n - 1)
        have rec_app : fact n = n * fact ((↑n : Int) - 1).toNat := by
            conv_lhs => unfold fact
            rw [if_neg (by omega : n ≠ 0)]
        have e : ((↑n : Int) - 1).toNat = n - 1 := by omega
        rw [e] at rec_app
        have h_prod : 1 * 1 <= n * fact (n - 1) := by
            apply Nat.mul_le_mul <;> omega
        omega
    )
}
```

A self-recursive proof (the strong-induction shape from Chapter 3, though one-step recursion would do). The recursive case unfolds `fact` once to get `fact n = n * fact(n-1)`, uses the IH (`fact(n-1) ≥ 1`) and `n ≥ 1`, and `Nat.mul_le_mul` to conclude `n · fact(n-1) ≥ 1 · 1`. Worth knowing up front: the *monotonicity* proof below doesn't actually invoke this lemma (it gets what it needs from `m ≥ 1`). `fact_pos` is here as a clean standalone example of the self-recursive positivity shape — see Exercise 2.

### `fact_monotone`: `k ≤ m ⟹ k! ≤ m!`

```rust
proof fn fact_monotone(k: nat, m: nat)
    requires k <= m
    ensures fact(k) <= fact(m)
    decreases m - k
by {
    if h : k = m then (
        subst h; omega
    ) else (
        have ih := fact_monotone k (m - 1)
        have ih_app := ih (by omega)
        have step : fact (m - 1) <= fact m := by
            have rec_app : fact m = m * fact ((↑m : Int) - 1).toNat := by
                conv_lhs => unfold fact
                rw [if_neg (by omega : m ≠ 0)]
            have e : ((↑m : Int) - 1).toNat = m - 1 := by omega
            rw [e] at rec_app
            have h_step : 1 * fact (m - 1) <= m * fact (m - 1) := by
                apply Nat.mul_le_mul_right; omega
            omega
        omega
    )
}
```

Monotonicity chains one-step growth: `fact(m) = m · fact(m−1) ≥ 1 · fact(m−1) = fact(m−1)` (using `m ≥ 1`), and the IH carries `fact(k) ≤ fact(m−1)`. The `decreases m - k` measure shrinks as `m` walks down toward `k`.

### `fact_10_bound`: `10! ≤ 3628800`

```rust
proof fn fact_10_bound()
    ensures fact(10 as nat) <= 3628800
by {
    repeat unfold fact
    decide
}
```

A concrete value, used to make the overflow check numeric. Here `repeat unfold fact` *is* the right move — unlike `fib` (Chapter 2), `fact` has a **single** recursive call and no dead `else`-branches for `repeat` to over-expand, so it unfolds cleanly down a straight line and `decide` evaluates `10! = 3628800`.

## The iterative function

```rust
#[verifier::tactus_auto]
fn factorial(n: u64) -> (r: u64)
    requires n <= 10
    ensures r as nat == fact(n as nat)
{
    let mut result: u64 = 1;
    let mut i: u64 = 0;
    assert(result as nat == fact(i as nat)) by {
        intros
        have h : i.toNat = 0 := by omega
        rw [h]; unfold fact; decide
    };
    while i < n
        invariant
            i <= n,
            n <= 10,
            result as nat == fact(i as nat),
            result <= 3628800,
        decreases n - i
    {
        // (1) recurrence: fact(i+1) = (i+1) * fact(i)
        assert(fact((i + 1) as nat) == (i + 1) * fact(i as nat)) by { … };
        // (2) bound: result * (i + 1) <= 3628800
        assert(result * (i + 1) <= 3628800) by { … };
        // (3) bridge: result * (i + 1) = fact(i+1)  -- needed for maintain
        assert(result * (i + 1) == fact((i + 1) as nat)) by { … };
        result = result * (i + 1);
        i = i + 1;
    }
    result
}
```

The bound `n <= 10` keeps us inside `fact_10_bound`'s range; `10! = 3628800` fits comfortably in `u64`. (You could push the precondition to `n <= 20` — `20!` is the largest factorial under `u64::MAX` — with a bigger concrete bound lemma. Exercise 3.)

### The loop-body assert chain

The invariant is `result == fact(i)`, and the body does `result = result * (i + 1)` then `i = i + 1`. To carry the invariant across one iteration we need to know that the *new* `result` (`= old_result * (i + 1)`) equals `fact(i + 1)`. Three asserts build that, in order:

1. **Recurrence** — `fact(i + 1) == (i + 1) * fact(i)`. One unfold of `fact`, dropping the `== 0` base case. This is the densest proof in the tutorial: the loop variables are `u64` (rendered as `Int`) but `fact` is `nat`-valued, so it juggles a `.toNat` cast on the recursive index and a `zify` to lift the resulting `Nat` equation up to `Int` before `linarith` closes. The inline comments in the `.rs` walk through each step.
2. **Overflow bound** — `result * (i + 1) <= 3628800`. This is the obligation that *needs a helper*: it invokes `fact_monotone(i + 1, 10)` to get `fact(i+1) ≤ fact(10)`, then `fact_10_bound` for `fact(10) ≤ 3628800`, and `nlinarith` combines them with the invariant `result == fact(i)`. No tactic string could have supplied those two lemma applications — hence the explicit assert.
3. **Maintain bridge** — `result * (i + 1) == fact((i + 1))`. Given (1) and the invariant, this is `nlinarith` chaining `result * (i+1) = fact(i) * (i+1) = (i+1) * fact(i) = fact(i+1)`.

With (3) proved *before* the assignment, the assignment `result = result * (i + 1)` re-establishes `result == fact(i + 1)`, and (2) makes its overflow check close. Then `i = i + 1` advances the index and the invariant `result == fact(i)` holds again.

> **A note on order.** The asserts come *before* the assignments, while `result` and `i` still hold their old values — so `fact(i)` in the asserts refers to the pre-step state. This is the same discipline as a hand-written loop-invariant proof: establish the recurrence about the next state, *then* take the step.

## Why this would be painful in Z3

Everything from chapters 1–3 applies — Z3 has no native induction, so `fact_pos`, `fact_monotone`, and the recurrence would each need hand-rolled recursive proof functions with `reveal_with_fuel` tuning. On top of that, the recurrence-based invariant forces the verifier to unfold `fact` at the loop boundary on *every* iteration's obligation, which is exactly the kind of controlled-unrolling-under-a-loop that burns Z3 rlimit. Lean's `decreases`-checked recursion plus `unfold`/`rw` makes each step explicit and cheap.

## Exercises

1. **`pow_iter`.** Define `pow(base: nat, e: nat)` recursively and write an iterative `pow_iter(base, e)` verified against it. Same multiplicative-recurrence shape; the overflow bound needs care (pick a small precondition like `base <= 2, e <= 60`).
2. **Spot the unused helper.** `fact_pos` (`n! ≥ 1`) is never invoked by `fact_monotone` or by the loop — the monotonicity step gets `m · fact(m−1) ≥ 1 · fact(m−1)` from `m ≥ 1` (via `Nat.mul_le_mul_right`), not from positivity. Delete `fact_pos` and re-verify: everything else still passes and the count drops to `8`. It's kept in the file as a compact standalone example of the self-recursive positivity proof — but if you'd rather it earn its keep, rewrite monotonicity's `step` sub-proof to route through `fact_pos` explicitly.
3. **Push the bound to `n <= 20`.** Replace `fact_10_bound` with a `fact_20_bound` (`20! = 2432902008176640000`, which fits in `u64`), bump the precondition and the `result <= …` invariant, and re-verify. Does `repeat unfold fact; decide` still compute `20!` within budget, or do you need explicit unfolds?

## What's next

This is the current frontier of the tutorial. The natural Chapter 5 continues with **fast** algorithms verified against simple specs — `pow_by_squaring` against `pow` (O(log e)), the Euclidean `gcd`, or the fast-doubling Fibonacci that Chapter 3's addition formula unlocked. Each reuses this chapter's template: a recurrence-based invariant, a handful of helper lemmas, and an assert chain in the loop body.
