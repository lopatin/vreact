// expect: fail nonzero-divisor non-null ratio=incomplete look=incomplete
// assert(c) evaluates c where control reaches it, and implies evaluates both arguments:
// ratio(1, 0) throws "idiv by zero" and look(new Map(), 3) reads `.v` of undefined, although
// both calls meet the contracts. The obligations of the consequent must hold without the antecedent.
import { requires, assert, implies, idiv, type int } from "vreact/spec";

type Item = { readonly v: int };

export function ratio(a: int, b: int): int {
  requires(b >= 0);
  assert(implies(b !== 0, idiv(a, b) === idiv(a, b)));
  return a;
}

export function look(m: ReadonlyMap<int, Item>, k: int): int {
  assert(implies(m.has(k), m.get(k)!.v === m.get(k)!.v));
  return k;
}
