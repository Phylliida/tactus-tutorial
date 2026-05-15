# tactus-tutorial

Proving stuff about Rust with Lean.

[Tactus](https://github.com/Phylliida/tactus) is a fork of [Verus](https://github.com/verus-lang/verus) that replaces the Z3 SMT backend with Lean 4. Z3 is great at linear arithmetic and bit-blasting, but it struggles with induction, recursion, and the kinds of combinatorial identities that mathematicians actually care about. Lean handles those naturally — and gives you human-readable, structured proofs as a bonus.

This tutorial is for readers with **some** familiarity with Rust and Lean, but no deep expertise in either. If you've used Sage, written a bit of Rust, and seen induction proofs before, you're in the target audience.

## Setup

You need a working build of Tactus and a Mathlib download. Both are one-time.

```bash
# 1. Clone tactus next to this repo (assumed at ../tactus)
git clone https://github.com/Phylliida/tactus.git ../tactus

# 2. Build vargo, then Tactus
cd ../tactus/tools/vargo && cargo build --release && cd ../../source
PATH="../tools/vargo/target/release:$PATH" vargo build --release

# 3. Download precompiled Mathlib (~2 GB, takes 2–5 minutes)
cd lean_verify && ./scripts/setup-mathlib.sh
```

Confirm Lean is on `$PATH` (`which lake` should succeed). If you used `elan`, add the toolchain bin dir to your `PATH`:

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH"
```

To verify a chapter:

```bash
../tactus/source/target-verus/release/verus chapters/01-sum-to-n/sum_to_n.rs
```

Expected output: `verification results:: N verified, 0 errors`.

See [`tactus/DESIGN.md`](../tactus/DESIGN.md) for the architecture.

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

- Chapter 1: ⏳ in progress
- Chapters 2–5: not yet started
