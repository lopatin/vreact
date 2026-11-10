// expect: fail nonzero-divisor
// assume(c) trusts c, but JS still evaluates c (vreact/spec's assume is a function): split(1, 0)
// throws "idiv by zero" evaluating the consequent of implies, so its divisor obligation must
// hold without the antecedent.
import { assume, implies, idiv, type int } from "vreact/spec";

export function split(a: int, b: int): int {
  assume(implies(b !== 0, idiv(a, b) >= 0));
  return a;
}
