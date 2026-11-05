// expect: verified
// The basic range facts of indexOf/findIndex: -1 ≤ r < length, r ≥ 0 exactly when an element
// matches, and the element at a found index matches. They are instantiated for every call
// (like a contract), so they also reach `omega`/`simp_all`, not only `grind`.
import { requires, ensures, type int } from "vreact/spec";

type Item = { readonly id: int; readonly name: string };

export function idx(xs: readonly int[], v: int): int {
  ensures((r: int) => r >= -1);
  return xs.indexOf(v);
}

export function idxRange(xs: readonly string[], v: string): int {
  ensures((r: int) => -1 <= r && r < xs.length);
  return xs.indexOf(v);
}

export function idxFound(xs: readonly string[], v: string): boolean {
  ensures((r: boolean) => r === xs.includes(v));
  return xs.indexOf(v) >= 0;
}

export function fidx(xs: readonly Item[], id: int): int {
  ensures((r: int) => r >= -1 && r < xs.length);
  return xs.findIndex((x) => x.id === id);
}

export function fidxFound(xs: readonly Item[], id: int): boolean {
  ensures((r: boolean) => r === xs.some((x) => x.id === id));
  return xs.findIndex((x) => x.id === id) >= 0;
}

export function fidxAt(xs: readonly Item[], id: int): string {
  ensures((r: string) => r === "" || xs.some((x) => x.id === id));
  const i = xs.findIndex((x) => x.id === id);
  if (i >= 0) return xs[i].name;
  return "";
}

export function fidxPoints(xs: readonly Item[], id: int): int {
  ensures((r: int) => r === -1 || xs[r].id === id);
  return xs.findIndex((x) => x.id === id);
}

export function idxPoints(xs: readonly int[], v: int): int {
  ensures((r: int) => r === -1 || xs[r] === v);
  return xs.indexOf(v);
}

export function fidxNext(xs: readonly Item[], id: int, n: int): int {
  requires(n === xs.length);
  ensures((r: int) => r <= n);
  return xs.findIndex((x) => x.id === id) + 1;
}
