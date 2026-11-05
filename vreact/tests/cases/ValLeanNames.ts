// expect: verified
// VTS names that are Lean keywords, root-level Lean names or names Lean generates for a type
// (functions show/some/id/max, locals matches/using/rec, fields rec/mk/matches, a type List).
import { ensures, type int } from "vreact/spec";

type List = { readonly rec: int; readonly mk: int; readonly matches: int };
type Mode = "rec" | "casesOn" | "open";

export function show(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}

export function some(l: List): int {
  ensures((r: int) => r === l.rec + l.mk + l.matches);
  const matches = l.matches;
  const using = l.mk;
  const rec = l.rec;
  return rec + using + matches;
}

export function id(m: Mode): boolean {
  return m === "rec";
}

export function max(a: int, b: int): int {
  ensures((r: int) => r >= a && r >= b);
  return a > b ? a : b;
}

export function callAll(): int {
  ensures((r: int) => r === 9);
  const l: List = { rec: 1, mk: 2, matches: 3 };
  return show(some(l)) + max(1, 2);
}

export function clearAll(cells: readonly string[]): readonly string[] {
  ensures((r: readonly string[]) => r.length === cells.length);
  return cells.map(() => "");
}
