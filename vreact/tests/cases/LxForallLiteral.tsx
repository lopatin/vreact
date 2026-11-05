// expect: verified
// P56: bounded quantifiers `forall(lo, hi, i => xs[i] …)` in contracts. With a numeral bound the
// index proofs under the binder made `grind` (Lean 4.35's arithmetic normaliser) raise `maximum
// recursion depth`; `vreact_bounded` replaces such a hypothesis by its parts with the index proofs
// as binders of their own, and instantiates the quantifier at the indices of the goal (also at a
// numeral index `xs[0]`, which E-matching on `xs[i.toNat]` does not find). A goal of that shape
// is split: the guard, then one case per value of `i`.
import { useState } from "react";
import { requires, ensures, invariant, forall, type int } from "vreact/spec";

export function sum3(xs: readonly int[]): int {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0));
  ensures((r: int) => r >= 0);
  return xs[0] + xs[1] + xs[2];
}

export function first(xs: readonly int[]): int {
  requires(xs.length > 0 && forall(0, xs.length, (i) => xs[i] >= 0));
  ensures((r: int) => r >= 0);
  return xs[0];
}

export function firstTwo(xs: readonly int[]): int {
  requires(xs.length >= 2 && forall(0, xs.length, (i) => xs[i] >= 1));
  ensures((r: int) => r >= 2);
  return xs[0] + xs[1];
}

// the quantifier at a variable index still works
export function at(xs: readonly int[], k: int): int {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0) && 0 <= k && k < 3);
  ensures((r: int) => r >= 0);
  return xs[k];
}

// establishing a numeral-bounded quantifier
export function bump3(xs: readonly int[]): readonly int[] {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0));
  ensures((r: readonly int[]) => r.length === 3 && forall(0, 3, (i) => r[i] >= 1));
  return [xs[0] + 1, xs[1] + 1, xs[2] + 1];
}

export function Grid() {
  const [cells, setCells] = useState<readonly int[]>([0, 0, 0]);
  invariant(cells.length === 3 && forall(0, 3, (i) => cells[i] >= 0));
  return (
    <div>
      <p>{cells[0] + cells[1]}</p>
      <button onClick={() => setCells([1, 2, 3])}>set</button>
      <button onClick={() => setCells([cells[0] + 1, cells[1], cells[2]])}>inc</button>
    </div>
  );
}

// three chained guarded invariants whose later conditions index
export function Chain() {
  const [i, setI] = useState<readonly int[]>([1]);
  invariant(i.length > 0);
  invariant(i[0] >= 1);
  invariant(i[0] <= 10);
  return (
    <div>
      <p>{i[0]}</p>
      <button onClick={() => { if (i[0] < 10) setI([i[0] + 1]); }}>inc</button>
      <button onClick={() => setI([1, ...i])}>push</button>
    </div>
  );
}
