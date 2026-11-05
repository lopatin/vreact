# Verified React — a formally verified React code-generation skill

| | |
|---|---|
| **The skill** | `.claude/skills/verified-react/` (source: `vreact/skill/verified-react/`). Teaches Claude to write React in a verifiable TypeScript subset, verify it, synthesize parts of it, and iterate to a kernel-checked certificate. |
| **The tool** | `vreact/`: TS→Lean 4 translator, React semantic model and runtime soundness proof in Lean, proof automation, synthesizer. See `vreact/README.md`. |
| **The model** | `vreact/docs/SEMANTICS.md`: what "verified" means here, and exactly what is trusted. |
| **The walkthrough** | `docs/WALKTHROUGH.md`: building `examples/kanban` incrementally, spec-first, synthesis, top-down with trusted stubs, bugs caught, to a fully verified app (79 obligations, certificate on standard axioms only). Raw outputs are in `docs/walkthrough/`. |
| **The app** | `examples/kanban` (`npm run dev` in that folder) and its verification (`npx vreact verify`). |

Quick check:

```bash
cd examples/kanban && node ../../vreact/bin/vreact.js verify
```
