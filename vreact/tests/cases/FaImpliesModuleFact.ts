// expect: fail index
// A module-level assert(c) runs when the module loads, and implies evaluates both arguments:
// with XS = [] loading the module reads XS[0].v and throws a TypeError, although the fact holds
// as an implication. The index obligation of the consequent must hold without the antecedent.
import { assert, implies, type int } from "vreact/spec";

type Item = { readonly v: int };

/** @opaque */
export const XS: readonly Item[] = [];
assert(implies(XS.length > 0, XS[0].v > 0));

export function first(): int {
  return XS.length;
}
