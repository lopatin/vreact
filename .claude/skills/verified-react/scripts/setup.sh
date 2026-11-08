#!/usr/bin/env bash
# Set up vreact: Node check, Lean 4 toolchain check, build the VReact Lean library,
# and (optionally) wire an app: `setup.sh /path/to/app` (npm i the tool, vreact.json, .gitignore,
# lean-toolchain + lakefile.toml for Lean editors).
set -euo pipefail
SKILL_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOL="$SKILL_DIR/tool"
[ -d "$TOOL" ] || { echo "error: $TOOL (the vreact package) not found"; exit 1; }

node_major=$(node -p 'process.versions.node.split(".")[0]' 2>/dev/null || echo 0)
node_minor=$(node -p 'process.versions.node.split(".")[1]' 2>/dev/null || echo 0)
if [ "$node_major" -lt 22 ] || { [ "$node_major" -eq 22 ] && [ "$node_minor" -lt 6 ]; }; then
  echo "error: Node >= 22.6 required (TypeScript type stripping); found $(node -v 2>/dev/null || echo none)"; exit 1
fi

LAKE="$(command -v lake || true)"
[ -z "$LAKE" ] && [ -x "$HOME/.elan/bin/lake" ] && LAKE="$HOME/.elan/bin/lake"
if [ -z "$LAKE" ]; then
  echo "Lean 4 is not installed. Install the official toolchain manager (elan) with:"
  echo "  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none"
  echo "then re-run this script (the Lean version is pinned by $TOOL/lean/lean-toolchain)."
  exit 2
fi

echo "› npm install (tool)"
(cd "$TOOL" && npm install --silent)
echo "› building the VReact Lean library (first time: ~1 min)"
(cd "$TOOL/lean" && "$LAKE" build 2>&1 | tail -1)

if [ "${1:-}" != "" ]; then
  APP="$(cd "$1" && pwd)"
  echo "› wiring app $APP"
  (cd "$APP" && npm install --silent "$TOOL")
  [ -f "$APP/vreact.json" ] || printf '{ "src": "src", "exclude": ["main.tsx"], "proofs": "proofs", "out": ".vreact" }\n' > "$APP/vreact.json"
  grep -q '"strict": *true' "$APP/tsconfig.json" 2>/dev/null || echo "warning: set \"strict\": true in $APP/tsconfig.json"
  grep -q '^\.vreact' "$APP/.gitignore" 2>/dev/null || echo ".vreact/" >> "$APP/.gitignore"
  # Lean editors (lean4ij, VS Code) opened on the app folder: lean-toolchain + lakefile.toml
  # (never over a lakefile of the user's; `vreact verify` keeps vreact's own up to date)
  node --no-warnings --experimental-strip-types "$TOOL/src/ide.ts" "$APP"
  echo "done: run 'npx vreact verify' in $APP (after that, a Lean editor opened on $APP checks the proofs/*.lean files)"
else
  echo "done: run 'node $TOOL/bin/vreact.js verify' in an app (or pass the app path to this script)"
fi
