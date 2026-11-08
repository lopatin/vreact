// expect: status verdict=not-verified errors=proof same=incomplete why.same=kernel~re-check proved=0 unchecked=1
// What a proof module added, checked after the build (backstop of round-2 finding
// r4-lean-r2-env-mismatch). smuggled/Base.lean (put in place after the translation: the whitelist
// rejects it, RejectRlEnvImports) hides a global `macro_rules` from a check that parses it in
// the wrong environment; imported by every generated module, it turned the generated
// `same x = x + 1` into `True`, and same's false ensures was VERIFIED with no axioms. The kernel
// re-check (`vreact-certify`) finds the macro's entry in Proofs.Base's environment extensions: a
// proof module may add theorems, definitions and simp/grind attributes, nothing else, so
// Proofs.Base and every module importing it are not certified.
import { ensures, type int } from "vreact/spec";

// false: same(0) is 0, not 1
export function same(x: int): int {
  ensures((r: int) => r === x + 1);
  return x;
}
