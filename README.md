# tactus-tutorial

Proving stuff about Rust with Lean.

[Tactus](https://github.com/Phylliida/tactus) is a fork of [Verus](https://github.com/verus-lang/verus) that replaces the Z3 SMT backend with Lean 4. Z3 is great at linear arithmetic and bit-blasting, but it struggles with induction, recursion, and the kinds of combinatorial identities that mathematicians actually care about. Lean handles those naturally — and gives you human-readable, structured proofs as a bonus.

This tutorial is for readers with **some** familiarity with Rust and Lean, but no deep expertise in either. If you've used Sage, written a bit of Rust, and seen induction proofs before, you're in the target audience.

## Setup

See [Chapter 0](chapters/00-setup/README.md) for a detailed setup walkthrough — prerequisites, building Tactus, downloading Mathlib, PATH wrangling, and troubleshooting. The very short version:

```bash
git clone https://github.com/Phylliida/tactus.git ../tactus
cd ../tactus/tools/vargo && cargo build --release && cd ../../source
PATH="../tools/vargo/target/release:$PATH" vargo build --release
cd lean_verify && ./scripts/setup-mathlib.sh
```

Then verify a chapter:

```bash
../tactus/source/target-verus/release/verus --lean-backend chapters/01-sum-to-n/sum_to_n.rs
```

Expected output: `verification results:: N verified, 0 errors`.

See [`tactus/DESIGN.md`](../tactus/DESIGN.md) for the architecture.

## A note on `simp`

Mathlib convention says **never use `simp` for an intermediate step** — only as a closing tactic. The reason: `simp`'s behavior is governed by Mathlib's `@[simp]` lemma set, which evolves. Code that calls `simp` and then expects a *specific* intermediate goal shape for subsequent tactics will break when a future Mathlib update changes what `simp` produces.

The chapters here follow this convention. Where chapter 1 might naively write:

```rust
unfold sum_to; simp; nlinarith [ih]   -- ✗ intermediate simp
```

we instead write:

```rust
unfold sum_to
rw [if_neg (by omega : (k + 1 : Nat) ≠ 0)]
rw [show ((↑(k + 1) : Int) - 1).toNat = k from by omega]
nlinarith [ih]                          -- ✓ pinned lemmas all the way down
```

It's more verbose, but every step is stable: `if_neg` is a core Lean lemma, and the `rw [show … from by omega]` form names *exactly* what's being rewritten.

`simp` as a *closing* tactic is fine — that's just "if simp doesn't close it, the proof fails," which is the same failure mode as any other closer. You'll see closing `simp` calls in `fib_seven` (computing a concrete value), the base cases of `fib_addition`, and a few helper lemmas. The chapters flag intermediate-vs-closing in inline comments where it matters.

## Planned chapters

The arc moves from "induction in one line" to "verify a real Rust algorithm against a mathematical spec." Starred (⭐) examples are the headline cases that most clearly show Lean's advantage over Z3.

### 1. Induction warm-ups

Simple one-line specs that Z3 cannot close without manual ladder lemmas, but Lean dispatches with a single `induction` tactic.

- `sum_to_n`: 1 + 2 + … + n = n(n+1)/2 ⭐
- `sum_odd`: 1 + 3 + … + (2n−1) = n²
- `sum_squares`: ∑ k² = n(n+1)(2n+1)/6
- `sum_powers_of_two`: 1 + 2 + 4 + … + 2ⁿ = 2ⁿ⁺¹ − 1

### 2. Recursive function correctness

The signature Tactus use case: an iterative Rust implementation matches a recursive mathematical spec.

- `factorial`: iterative loop ≡ recursive spec
- `pow_by_squaring`: fast exponentiation ≡ xⁿ ⭐
- `gcd`: Euclidean algorithm ≡ mathematical gcd
- Fibonacci: two-variable iterative loop ≡ recursive `fib`

### 3. Combinatorial identities

Where Sage-flavored intuition pays off — proofs about binomial coefficients.

- Pascal's rule: C(n, k) = C(n−1, k−1) + C(n−1, k)
- Row sum: ∑ C(n, k) = 2ⁿ ⭐
- Hockey stick: ∑ C(i, k) = C(n+1, k+1)
- Vandermonde: ∑ C(m, k)·C(n, r−k) = C(m+n, r)
- Catalan: recurrence ↔ closed form C(2n, n)/(n+1)

### 4. Fibonacci identities

Strong induction and chained rewrites — the kind of proof Z3 won't even attempt.

- Sum identity: ∑ Fᵢ = F_{n+2} − 1
- Cassini: F_{n−1}·F_{n+1} − Fₙ² = (−1)ⁿ
- Addition formula: F_{m+n} = Fₘ·F_{n+1} + F_{m−1}·Fₙ
  - Opens the door to an O(log n) Fibonacci algorithm

### 5. Algorithmic capstones

Pulling it all together with real Rust algorithms verified against mathematical specs.

- Tower of Hanoi: move count = 2ⁿ − 1 ⭐
- Insertion sort: sorted + is_permutation
- Binary search: correctness + termination
- Lattice paths: counting paths in an n×n grid = C(2n, n)

## Status

- Chapter 0: ✅ drafted (setup and toolchain)
- Chapter 1: ✅ drafted (`sum_to_n`)
- Chapter 2: ✅ drafted (Fibonacci identities — moved up from the original Chapter 4 slot)
- Chapter 2.5 (optional): ✅ drafted (Fibonacci, encoded over `int` instead of `nat` — alternative encoding for readers who want to see the trade-off)
- Chapter 3: ✅ drafted (strong induction via `fib(n) ≤ 2ⁿ`)
- Chapter 4: ✅ drafted (iterative factorial against recursive `fact` spec — landed after the synthetic-temp closer fix)
- Chapter 5: ✅ drafted (exponentiation by squaring against recursive `pow` — the O(log n) capstone)

The chapter order shifted from the original outline: exec-fn verification (originally slated for an early `factorial` chapter) was deferred while Tactus's `as nat`-into-recursive-spec-fn tooling matured, so the early chapters are proof-fn-first and build up the techniques (induction, strong induction, rewriting). That tooling has since landed, and exec verification now appears throughout — `sum_iter` (Chapter 1), `fib_iter` (Chapter 2), `factorial` (Chapter 4), and the fast-exponentiation capstone `pow_iter` (Chapter 5).
