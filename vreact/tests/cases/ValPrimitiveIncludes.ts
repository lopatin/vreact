// expect: verified
// includes / indexOf / distinct compare primitive values (by value in JS too); a fromIndex is
// written as a slice; record membership goes through a key.
import { ensures, implies, distinct, type int } from "vreact/spec";

type Tag = "a" | "b";
type Pt = { readonly id: int; readonly x: int };

export function seenAgain(xs: readonly int[]): boolean {
  ensures((r: boolean) => r === (xs.length > 0 && xs.slice(1).includes(xs[0])));
  if (xs.length === 0) return false;
  return xs.slice(1).includes(xs[0]);
}

export function hasTag(ts: readonly Tag[]): boolean {
  ensures((r: boolean) => r === ts.includes("a"));
  return ts.includes("a");
}

export function firstB(ss: readonly string[]): int {
  return ss.indexOf("b");
}

export function containsPt(ps: readonly Pt[], p: Pt): boolean {
  ensures((r: boolean) => implies(r, ps.length > 0));
  return ps.some((q) => q.id === p.id);
}

export function ids(ps: readonly Pt[]): boolean {
  return distinct(ps, (p) => p.id);
}
