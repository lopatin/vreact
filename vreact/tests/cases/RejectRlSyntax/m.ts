// expect: reject proofs/m.lean:5:1: `macro "grind" : tactic => ;; proofs/m.lean:6:1: `macro_rules | ;; proofs/m.lean:7:1: `syntax "bump" : term` ;; proofs/m.lean:8:1: `notation ;; proofs/m.lean:9:1: `infixl:65 ;; proofs/m.lean:10:1: `elab "zz" ;; proofs/m.lean:12:1: `simproc forgeOk ;; proofs/m.lean:13:1: `declare_syntax_cat ;; syntax extensions (macro, macro_rules, syntax, notation, elab, …) change how the generated code and vreact's tactics parse ;; simprocs and grind propagators run code inside the automation
// Syntax extensions and code inside the automation in a user proof (R4 item 12):
// proofs/m.lean is imported by use.ts's generated Defs, so a `macro "grind"` or a `macro_rules`
// for vreact_auto there changes how use's obligations are elaborated, `syntax` turns names of the
// generated code into keywords, a simproc runs inside vreact_auto. All are rejected before Lean
// runs (also behind `open … in`); the automation is extended only by tagged lemmas.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
