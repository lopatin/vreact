// expect: fail postcondition verdict=not-verified errors=proof plus=incomplete keep=incomplete why.keep=kernel~re-check proved=0
// An instance and an axiom from a proof module (backstop of round-2 finding
// r4-lean-r2-env-mismatch, whose sibling smuggled them through `import VReact.JS`).
// smuggled/Base.lean (put in place after the translation: the whitelist rejects it) declares
// `axiom ax : False` and a high-priority `HAdd Int Int Int` instance that returns the left
// operand, both in effect in every generated module. Lean elaborates them without complaint; the
// report used to judge each item on its own messages (plus's false ensures fails, keep is
// VERIFIED). The kernel re-check finds the instance's entry and the axiom in Proofs.Base: it and
// every module importing it are not certified, so nothing elaborated after it is VERIFIED.
import { ensures, type int } from "vreact/spec";

// false: plus(0, 1) is 1, not 0
export function plus(x: int, y: int): int {
  ensures((r: int) => r === x);
  return x + y;
}

export function keep(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
