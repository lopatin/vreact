// expect: verified
// Guards in contracts: `&&`, `||`, `?:`, forall bounds and every membership are in scope for the
// index obligations they guard (as JS short-circuit evaluation guarantees); implies only in an
// ensures, which JS never runs (FaImpliesRequiresFn: elsewhere it evaluates both arguments).
import { useState } from "react";
import { requires, ensures, invariant, implies, forall, type int } from "vreact/spec";

export function at(xs: readonly int[], i: int): int {
  requires(0 <= i && i < xs.length && xs[i] > 0);
  ensures((r: int) => r > 0);
  return xs[i];
}

export function same(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.length === 0 || r[0] === xs[0]);
  return xs;
}

export function headOr(xs: readonly int[], d: int): int {
  ensures((r: int) => implies(xs.length > 0, r === xs[0]));
  ensures((r: int) => (xs.length > 0 ? r === xs[0] : r === d));
  return xs.length > 0 ? xs[0] : d;
}

export function allNonNeg(xs: readonly int[]): boolean {
  requires(forall(0, xs.length, (i) => xs[i] >= 0));
  return true;
}

export function rowsNonEmpty(rows: readonly (readonly int[])[]): boolean {
  requires(rows.every((r) => r.length > 0 && r[0] >= 0));
  return forall(0, rows.length, (i) => rows[i].length > 0);
}

type Item = { readonly id: int; readonly qty: int };

export function Sel() {
  const [items] = useState<readonly Item[]>([{ id: 1, qty: 2 }]);
  const [sel, setSel] = useState<int>(-1);
  invariant(sel === -1 || (0 <= sel && sel < items.length && items[sel].qty > 0));
  return <button onClick={() => setSel(-1)}>{sel}</button>;
}
