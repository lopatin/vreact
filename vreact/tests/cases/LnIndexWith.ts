// expect: verified
/// <reference lib="es2023.array" />
// indexOf has the bounds of findIndex and points at the element; `with` keeps the length
// (so it can be chained) and reads back what it wrote.
import { requires, ensures, distinct, type int } from "vreact/spec";

export function lookup(xs: readonly string[], q: string): string {
  ensures((r: string) => r === q || r === "");
  const i = xs.indexOf(q);
  if (i >= 0) return xs[i];
  return "";
}

export function swapAdj(xs: readonly int[], i: int): readonly int[] {
  requires(0 <= i && i + 1 < xs.length);
  ensures((r: readonly int[]) => r.length === xs.length);
  const p = xs[i];
  const q = xs[i + 1];
  return xs.with(i, q).with(i + 1, p);
}

export function setThenGet(xs: readonly int[], i: int): int {
  requires(0 <= i && i < xs.length);
  ensures((r: int) => r === 7);
  const ys = xs.with(i, 7);
  return ys[i];
}

export function keysAfterSlice(ids: readonly int[]): readonly int[] {
  requires(distinct(ids));
  ensures((r: readonly int[]) => distinct(r));
  return ids.slice(1).toReversed();
}
