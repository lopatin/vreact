// expect: verified
// In requires, ensures and invariant too, an array callback that `(x) => condition` does not
// cover (a block body, a `function (x) { … }`) is read as code instead of being rejected ("every((x)
// => condition) with an expression body"): JS calls it on each element, so that is its meaning.
import { useState } from "react";
import { requires, ensures, invariant, type int } from "vreact/spec";

export function firstPos(xs: readonly int[]): int {
  requires(xs.length > 0 && xs.every((x) => { return x > 0; }));
  ensures((r: int) => r > 0);
  return xs[0];
}

export function allPos(xs: readonly int[]): readonly int[] {
  requires(xs.length > 0 && xs.every(function (x) { return x > 0; }));
  ensures((r: readonly int[]) => r.length > 0 && r.every((x) => { const y = x; return y > 0; }));
  return xs;
}

export const ONE: int = firstPos([1, 2]);

type P = { readonly start: int };
export function List(props: P) {
  requires(props.start >= 0);
  const [xs, setXs] = useState<readonly int[]>([props.start]);
  invariant(xs.every((x) => { return x >= 0; }));
  return <button onClick={() => setXs([...xs, xs.length])}>{xs.length}</button>;
}
