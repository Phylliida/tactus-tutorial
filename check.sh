#!/usr/bin/env bash
# Verify all tutorial chapters under the Lean backend, then assert the B6
# no-search gate claim over the emitted artifacts (DESIGN-transparent-automation.md
# §5: no artifact imports the search module / names a search-ladder tactic).
#
# Usage: ./check.sh
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERUS="$HERE/../tactus/source/target-verus/release/verus"
LEAN_BIN="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin"

if [[ ! -x "$VERUS" ]]; then
  echo "error: tactus verus binary not found at $VERUS" >&2
  exit 1
fi

# Lean resolution: PATH first, then elan, then the nix store.
if ! command -v lean >/dev/null; then
  for cand in "$HOME/.elan/toolchains"/*/bin /nix/store/*lean4-4.25.0/bin; do
    [[ -x "$cand/lean" ]] && export PATH="$cand:$PATH" && break
  done
fi

fail=0
# B6: same rationale as gt's check.sh — scan only the current emission.
find "$HERE/target/tactus-lean" -name '*.lean' -delete 2>/dev/null || true

for f in "$HERE"/chapters/*/*.rs; do
  if PATH="$LEAN_BIN:$PATH" "$VERUS" --lean-backend "$f" >/dev/null 2>&1; then
    echo "ok      $f"
  else
    echo "FAIL    $f"
    fail=1
  fi
done
[[ "$fail" -ne 0 ]] && exit 1

TOOLS="$(dirname "$(dirname "$(dirname "$VERUS")")")"
python3 "$TOOLS/tools/check-no-search.py" "$HERE/target/tactus-lean" || {
  echo "[check.sh] no-search gate claim FAILED — see above" >&2
  exit 1
}
echo "[check.sh] chapters green + no-search gate claim holds" >&2