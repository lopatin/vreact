// expect: verified
// implies(a, b) in contracts that run (requires, invariant, assert, a module-level assert):
// b is evaluated whatever a is, so b's own obligations hold without a — here from guards around
// the call (&&, an earlier requires / invariant, a quantifier's bounds or membership) or from
// the precondition; as a hypothesis `a → b` is used like any implication. In an ensures lambda
// (never called) b may still index under a, and `x === null || …` guards as JS evaluates it.
import { useState } from "react";
import { requires, ensures, invariant, assert, implies, forall, idiv, type int } from "vreact/spec";

type Item = { readonly v: int };

export function share(flag: boolean, total: int, n: int): int {
  requires(implies(flag, n > 0));
  return flag ? idiv(total, n) : 0;
}

export function shares(): int {
  return share(true, 10, 2) + share(false, 10, 0);
}

export function firstPos(xs: readonly Item[]): boolean {
  requires(xs.length > 0 && implies(xs[0].v > 0, xs[0].v >= 1));
  return true;
}

export function sorted(xs: readonly Item[]): boolean {
  requires(forall(1, xs.length, (i) => implies(xs[i - 1].v > 0, xs[i - 1].v <= xs[i].v)));
  requires(xs.every((x) => implies(x.v > 0, x.v !== 0)));
  return true;
}

export function headPos(xs: readonly int[]): boolean {
  requires(xs.length === 0 || xs[0] > 0);
  return true;
}

export function check(a: int, b: int): int {
  requires(b > 0);
  assert(implies(a > 0, idiv(a, b) === idiv(a, b)));
  return a;
}

export function head(xs: readonly Item[]): int {
  ensures((r: int) => implies(xs.length > 0, r === xs[0].v));
  return xs.length > 0 ? xs[0].v : 0;
}

/** @opaque */
export const XS: readonly Item[] = [{ v: 1 }];
assert(XS.length > 0 && implies(XS[0].v > 0, XS[0].v >= 1));

function Show(props: { readonly sel: Item | null }) {
  requires(props.sel === null || props.sel.v >= 0);
  return <p>shown</p>;
}

export function Panel() {
  const [items, setItems] = useState<readonly Item[]>([{ v: 1 }]);
  invariant(items.length > 0);
  invariant(implies(items.length > 1, items[0].v >= 0));
  return (
    <div>
      <Show sel={null} />
      <button onClick={() => setItems([{ v: 2 }, { v: 3 }])}>{items.length}</button>
    </div>
  );
}
