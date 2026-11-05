#!/usr/bin/env bash
# Replays every step of docs/OPTIONS_CHAIN_WALKTHROUGH.md and checks that the tool still says
# what the saved logs say.
#
# For each docs/options-chain/steps/NN-name/ (a full snapshot of src/ and, if any, proofs/):
#   1. copy it into a fresh temp project with the configs of examples/options-chain and a
#      node_modules symlink;
#   2. run the step's command (steps/NN-name/command), without --write;
#   3. compare the stable lines with docs/options-chain/NN-name.txt: the verdict line, the
#      per-item statuses (components, functions, certificates and their axioms, obligations by
#      file, failed obligations), VTS rejections, and synth's per-hole outcomes. Timings, random
#      test counts and Lean goals are ignored.
# Exits non-zero on any mismatch.
#
#   bash docs/options-chain/replay.sh            # all steps (about 15 minutes)
#   bash docs/options-chain/replay.sh 05 23      # only the steps whose names start with 05 or 23
#   bash docs/options-chain/replay.sh --stable docs/options-chain/26-final.txt   # the compared lines
#
# Requirements: Node >= 22.6, Lean via elan (~/.elan/bin), the VReact Lean library built
# (vreact/lean: lake build), and the app's npm dependencies (examples/options-chain/node_modules,
# e.g. from `bash vreact/skill/verified-react/scripts/setup.sh examples/options-chain`, or the
# examples/kanban ones). Synth searches have a 60 s budget per hole: on a much slower machine a
# fill found late (step 10 finds `cancel` after ~40 s) may not be found, and the replay reports it.
set -uo pipefail
export LC_ALL=C
export PATH="$HOME/.elan/bin:$PATH"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
APP="$REPO/examples/options-chain"
CLI="$REPO/vreact/bin/vreact.js"

nm=""
for cand in "$APP/node_modules" "$REPO/examples/kanban/node_modules"; do
  if [ -d "$cand/react" ] || [ -d "$cand/vreact" ]; then nm="$(cd "$cand" && pwd -P)"; break; fi
done
[ -n "$nm" ] || { echo "replay: no node_modules with react found (run setup.sh examples/options-chain)"; exit 2; }
[ -f "$CLI" ] || { echo "replay: $CLI not found"; exit 2; }

# The lines that must not change between runs, normalized.
stable() {
  sed -E $'s/\x1b\\[[0-9;]*m//g' "$1" |
    grep -E \
      -e '^translated [0-9]+ module' \
      -e '^  (VERIFIED\*?|INCOMPLETE|UNCHECKED|TRUSTED|ASSUMES) ' \
      -e '^  (✓|✗|\?) src/' \
      -e '^✗ src/[^ ]+ +\[' \
      -e '^✗ VTS ' \
      -e '^pending ' \
      -e '^trusted ' \
      -e '^(✔|✗|◐) ' \
      -e '^hole ' \
      -e '^  candidate passes ' \
      -e '^  ✔ proved by Lean' \
      -e '^  no verified solution for hole' |
    sed -E \
      -e 's/ +\([0-9.]+s\)$//' \
      -e 's/^  candidate passes [0-9]+ random tests: (.*)   \([0-9]+ candidate\(s\) tested in [0-9.]+s\)$/  candidate passes the random tests: \1/' \
      -e 's/^(  no verified solution for hole in [^:]+): .*/\1/'
}

if [ "${1:-}" = "--stable" ]; then # print the compared lines of a log
  stable "$2"
  exit 0
fi

TMP="$(mktemp -d "${TMPDIR:-/tmp}/vreact-replay.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

pass=0
fail=0
failed=()
for dir in "$HERE"/steps/*/; do
  name="$(basename "$dir")"
  if [ $# -gt 0 ]; then
    keep=0
    for p in "$@"; do case "$name" in "$p"*) keep=1 ;; esac; done
    [ $keep -eq 1 ] || continue
  fi
  log="$HERE/$name.txt"
  [ -f "$log" ] && [ -f "$dir/command" ] || { echo "✗ $name: missing log or command"; fail=$((fail + 1)); failed+=("$name"); continue; }
  # the step's command, without --write (the snapshot is the file synth searched in)
  read -r -a args < "$dir/command"
  run=()
  for a in "${args[@]}"; do [ "$a" = "--write" ] || run+=("$a"); done

  proj="$TMP/$name"
  mkdir -p "$proj"
  for f in vreact.json tsconfig.json package.json index.html vite.config.ts; do cp "$APP/$f" "$proj/"; done
  ln -s "$nm" "$proj/node_modules"
  cp -R "$dir/src" "$proj/src"
  [ -d "$dir/proofs" ] && cp -R "$dir/proofs" "$proj/proofs"

  start=$(date +%s)
  (cd "$proj" && node "$CLI" "${run[@]}") > "$proj/replay.txt" 2>&1
  secs=$(($(date +%s) - start))

  if diff <(stable "$log") <(stable "$proj/replay.txt") > "$proj/diff.txt"; then
    echo "✓ $name  (${run[*]}, ${secs}s)"
    pass=$((pass + 1))
  else
    echo "✗ $name  (${run[*]}, ${secs}s): stable lines differ (< saved, > now):"
    sed 's/^/    /' "$proj/diff.txt"
    fail=$((fail + 1))
    failed+=("$name")
  fi
  rm -rf "$proj"
done

echo
if [ $fail -eq 0 ]; then
  echo "replay: all $pass step(s) match their saved logs"
  exit 0
fi
echo "replay: $fail step(s) differ: ${failed[*]} ($pass match)"
exit 1
