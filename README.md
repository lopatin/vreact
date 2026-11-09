# Verified React — a formally verified React code-generation skill

| | |
|---|---|
| **The skill** | `.claude/skills/verified-react/` (source: `vreact/skill/verified-react/`). Teaches Claude to write React in a verifiable TypeScript subset, verify it, synthesize parts of it, and iterate to a kernel-checked certificate. |
| **The tool** | `vreact/`: TS→Lean 4 translator, React semantic model and runtime soundness proof in Lean, proof automation, synthesizer. See `vreact/README.md`. |
| **The model** | `vreact/docs/SEMANTICS.md`: what "verified" means here, and exactly what is trusted. |
| **The walkthrough** | `docs/WALKTHROUGH.md`: building `examples/kanban` incrementally, spec-first, synthesis, top-down with trusted stubs, bugs caught, to a fully verified app (79 obligations, certificate on standard axioms only). Raw outputs are in `docs/walkthrough/`. |
| **Options chain walkthrough** | [`docs/OPTIONS_CHAIN_WALKTHROUGH.md`](docs/OPTIONS_CHAIN_WALKTHROUGH.md): a medium-complexity trading widget (`examples/options-chain`: expiries, ATM strike, strike filter, heat map, order ticket, simulated feed) built step by step with real tool output. Part 1 builds it and ends with a mutation audit of the spec. Part 2 grows it: a precondition on dispatched actions, proved at every `dispatch` call; a cap on the total open order quantity, proved with a hand-written Lean proof file (`proofs/model.lean`); the simulated feed's rules (pause, rally) moved into a reducer; the UI state moved onto Maps and Sets, with generic helpers proved once for every key and value type their constraints allow; watched strikes; amending orders; and a second mutation audit. Every step's snapshot and log is in `docs/options-chain/`, re-checked by `docs/options-chain/replay.sh` (final app: 195 obligations, certificate on the three standard axioms only). |
| **The app** | `examples/kanban` (`npm run dev` in that folder) and its verification (`npx vreact verify`). |
| **More examples** | `examples/seats` (seat booking, opaque constant data), `examples/cart` (a small cart built step by step: model, synthesis, top-down App with a trusted stub, two bugs caught). |

## Getting started (fresh clone)

Requirements: Node ≥ 22.6 and Lean 4 via [elan](https://github.com/leanprover/elan)
(the Lean version is pinned in `vreact/lean/lean-toolchain`).

```bash
# installs the tool's npm deps, builds the Lean library, and wires the app
bash vreact/skill/verified-react/scripts/setup.sh examples/kanban
cd examples/kanban && npx vreact verify      # ✔ VERIFIED 79/79
npm run dev                                  # the same .tsx files, running in React 18
```

The other examples work the same way (`setup.sh examples/seats`, `setup.sh examples/cart`,
`setup.sh examples/options-chain`).
To use the skill from Claude Code, open this repository: it is installed at
`.claude/skills/verified-react/` (its `tool` link points at `vreact/`).
