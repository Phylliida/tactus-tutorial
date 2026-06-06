# Chapter 0: Setting up Tactus

This chapter walks through everything you need to verify the tutorial files on your own machine: getting Tactus built, getting Lean's Mathlib in place, and running a hello-world example to confirm the install works.

If you hit a snag, the troubleshooting section at the bottom covers the issues I ran into while writing the tutorial.

## What you need

- **Rust** with `rustup`. Tactus pins a specific stable toolchain via `rust-toolchain.toml`, so `rustup` will install it on first build.
- **Lean 4** via [elan](https://github.com/leanprover/elan), or via nix (`nix-shell -p lean4`). The pinned version is `v4.25.0` — `lean-project/lean-toolchain` in the Tactus repo is the source of truth if that ever shifts.
- **About 3 GB of disk** for the precompiled Mathlib download.
- **A C++ compiler** that rustc can find (for Verus's build).

Tactus has only been tested on Linux and macOS so far.

## Step 1: Clone Tactus

The tutorial assumes Tactus is at `../tactus` relative to this repo:

```bash
cd ..   # go to the directory containing tactus-tutorial/
git clone https://github.com/Phylliida/tactus.git
```

You can put it elsewhere; just adjust the paths in the `verus` invocations below.

## Step 2: Build `vargo`

`vargo` is Tactus's custom Cargo wrapper — it builds Verus with the right environment variables and toolchain. Build it first:

```bash
cd tactus/tools/vargo
cargo build --release
cd ../../source
```

If `rustup` warns that a toolchain isn't installed (e.g., `error: toolchain '1.94.0-…' is not installed`), run `rustup toolchain install` from the `tactus` repo root — `rustup` reads `rust-toolchain.toml` and installs the right version. **Don't** run the exact command rustup suggests; the project's pinned toolchain may differ.

## Step 3: Build Tactus

From `tactus/source`:

```bash
PATH="../tools/vargo/target/release:$PATH" vargo build --release
```

Expected output ends with something like:

```
verification results:: 1530 verified, 0 errors
```

That's vstd — the Verus standard library — being built and verified as part of the build. The whole step takes a few minutes on a warm cache, longer cold.

The produced binary is at `tactus/source/target-verus/release/verus`. You'll reference this in tutorial invocations.

## Step 4: Set up Mathlib

The tutorial proofs use Mathlib tactics (`nlinarith`, `linarith`, `ring`, …). Tactus's setup script downloads a precompiled Mathlib (about 2 GB, takes 2–5 minutes — much faster than building from source):

```bash
cd tactus/source/lean_verify
./scripts/setup-mathlib.sh
```

The script needs `lake` (Lean's package manager) and `lean` on `$PATH`. See the "Lean on PATH" troubleshooting below if `lake --version` doesn't work.

The script creates `~/.tactus/lean-project/` containing a `lakefile.lean` and a `.lake/` directory with the precompiled `.olean` files. Tactus's verifier auto-detects this directory at runtime.

## Step 4.5: Install the tutorial's helper lemmas

Chapter 2 onward use `import TactusTutorialHelpers` for a small set of `@[simp]` lemmas that clean up the `(↑(k + 1) - 1).toNat` shapes that arise from Verus's `(n - 1) as nat` casts. These are unconditional rewrites that omega could trivially prove but doesn't traverse into function arguments to find — so they have to live as simp lemmas to fire automatically.

The helper file lives at `tactus-tutorial/lean-helpers/TactusTutorialHelpers.lean`. To make it importable from your chapter files, symlink it into the Tactus lake project and register it in the lakefile:

```bash
# From the tutorial repo root:
ln -sf "$(realpath lean-helpers/TactusTutorialHelpers.lean)" \
    ../tactus/lean-project/TactusTutorialHelpers.lean

# Edit ../tactus/lean-project/lakefile.lean to add the lib:
#
#     lean_lib TactusTutorialHelpers where
#       srcDir := "."
#
# (Add right after the existing `lean_lib TactusCheck where ...` block.)
```

Then build the helpers once:

```bash
cd ../tactus/lean-project
lake build TactusTutorialHelpers
```

Subsequent verifies pick it up automatically. Without this step, chapters that say `import TactusTutorialHelpers` fail with `unknown module prefix`.

## Step 5: Run a tutorial chapter

From the tutorial repo root:

```bash
../tactus/source/target-verus/release/verus --lean-backend chapters/01-sum-to-n/sum_to_n.rs
```

Expected output (the `N` count varies by Tactus version — what matters is `0 errors`):

```
verification results:: N verified, 0 errors
```

If you see `0 errors`, everything's working. Try Chapter 2 next:

```bash
../tactus/source/target-verus/release/verus --lean-backend chapters/02-fibonacci/fibonacci.rs
# verification results:: N verified, 0 errors
```

## Step 6 (optional): An editor integration

Tactus has a Verus-style LSP, which gives you in-editor goal display, hover-to-see-types, and immediate feedback on proof failures. See the [official IDE support docs](https://verus-lang.github.io/verus/guide/ide_support.html) — the Tactus binary works as a drop-in replacement wherever the docs say `verus`.

For *just* verifying tutorial files at the command line, you don't need this.

## Anatomy of a tutorial file

Every chapter file follows the same skeleton:

```rust
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

import Mathlib.Tactic.Linarith       // ← Lean imports go here, at the top of `verus! { }`

spec fn ...                          // ← mathematical definitions
proof fn ...                         // ← theorems with Lean tactic proofs
fn main() {}                         // ← required even if empty

} // verus!
```

A few important details:

- **`use verus_builtin::*; use verus_builtin_macros::*;`** must come *outside* the `verus!` block. The macro itself comes from `verus_builtin_macros`.
- **`import …`** lines are *inside* the `verus! { }` block but *outside* any function. They mirror Lean's `import` syntax exactly — Tactus passes them through verbatim to the generated `.lean` file.
- **`fn main() {}`** is required even if your file has no executable code. It's a Rust requirement, not a Verus one.

## Reading verification output

A successful run prints one line:

```
verification results:: N verified, M errors
```

`N` counts the proof obligations Tactus checked (one per `proof fn`, plus per-obligation theorems for any `exec fn` with `#[verifier::tactus_auto]`). **The exact value of `N` depends on your Tactus version** — internal obligation bookkeeping shifts between releases — and isn't meaningful on its own. The check that matters is **`0 errors`**. For that reason the chapter examples below write the expected output as `N verified, 0 errors` rather than pinning a specific number.

When verification fails, Tactus prints the failing goal in Lean's standard notation, often with a hint about which tactic failed. It also drops the generated `.lean` file at:

```
<directory-of-rs-file>/target/tactus-lean/<file-basename>/<fn-name>.lean
```

Reading that file is invaluable when a proof isn't going through — you can see exactly what the goal looks like in Lean, including all the cast wrappers and refinement hypotheses Tactus added.

## Troubleshooting

### "lake: command not found" or Mathlib script fails

The setup script needs Lean's `lake` and `lean` binaries on `$PATH`. If you installed Lean via `elan`, this is usually handled by `~/.elan/bin/` — confirm with `which lake`.

If `~/.elan/bin/` isn't populated (some partial installs only populate `~/.elan/toolchains/`), prepend the toolchain's bin dir explicitly:

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH"
```

If you're on NixOS or using `nix-shell`, the simpler form is:

```bash
nix-shell -p lean4 --run ./scripts/setup-mathlib.sh
```

### "Lean 4 not found" when running `verus`

The verifier subprocess needs `lake`/`lean` on `$PATH` too. The most robust form for a tutorial-running command is:

```bash
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH" \
  ../tactus/source/target-verus/release/verus --lean-backend chapters/01-sum-to-n/sum_to_n.rs
```

Wrap that into a shell alias or a tiny `verify.sh` script if you'll be running it a lot.

### "vargo error: could not read Cargo.toml — run vargo in `source`"

`vargo` only works from inside `tactus/source/`. If you're elsewhere, `cd` in.

### Verification fails with `unknown tactic` for what looks like valid Lean

Tactus replaces tactic block contents with spaces during the Rust lexer pass and reads the original bytes back at verification time. One specific quirk: **`//` is not allowed inside a tactic block** — Rust's lexer treats it as a line comment that consumes the closing `}`. Use Lean's `--` line comment instead. (Block comments `/- -/` are fine.)

### "Application type mismatch: …has type Int but is expected to have type Nat"

You're hitting the `as nat` cast issue when passing a `u64` (or any u-typed value) to a `nat`-typed spec fn. This was a bug in earlier Tactus; if you're on the latest revision it should be fixed. If you still see it, see [`BUG-as-nat-cast.md`](../../../BUG-as-nat-cast.md) in the parent repo for the workaround and root-cause analysis.

### Build is very slow on first run

Verus's release build is in the 5–10 minute range cold. Vargo caches aggressively, so subsequent builds are seconds-fast unless you've touched Rust source in the Tactus repo itself.

`cargo clean` will wipe everything including caches — only do this if you're debugging a build-system issue. There's no reason to clean periodically.

## What's next

Once you've got Chapter 0 working, head to [Chapter 1](../01-sum-to-n/README.md) — the simplest induction proof, in about ten lines.
