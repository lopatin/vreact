// expect: verified
// Forms `vreact synth` now produces: `undefined` for optional fields, fills after early-return
// narrowing, two inline object-typed parameters, calls of a helper that has its own contract.
import { requires, ensures, implies, distinct, type int } from "vreact/spec";

export type Sel = { readonly items: int; readonly selected?: int };
export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };
export type Board = { readonly todo: readonly int[]; readonly done: readonly int[] };

export function clearSel(s: Sel): Sel {
  ensures((r: Sel) => r.selected === undefined && r.items === s.items);
  return { ...s, selected: undefined };
}

export function succ(x: int | null): int {
  ensures((r: int) => x === null || r === x + 1);
  if (x === null) return 0;
  return x + 1;
}

export function widthOf(s: Shape): int {
  requires(true);
  switch (s.kind) {
    case "circle":
      return 0;
    case "rect":
      return s.w;
  }
}

export function width(s: Shape): int {
  ensures((r: int) => r === widthOf(s));
  if (s.kind !== "rect") return 0;
  return s.w;
}

export function addX(a: { readonly x: int }, b: { readonly y: int; readonly z: int }): int {
  ensures((r: int) => r === a.x + b.y);
  return a.x + b.y;
}

/** @opaque */
export function addIfAbsent(xs: readonly int[], x: int): readonly int[] {
  ensures((r: readonly int[]) => r.includes(x) && xs.every((y) => r.includes(y)));
  ensures((r: readonly int[]) => implies(distinct(xs), distinct(r)));
  if (xs.includes(x)) return xs;
  return [...xs, x];
}

export function addTodo(b: Board, x: int): Board {
  ensures((r: Board) => r.todo.includes(x) && b.todo.every((y) => r.todo.includes(y)));
  ensures((r: Board) => implies(distinct(b.todo), distinct(r.todo)));
  ensures((r: Board) => r.done.length === b.done.length);
  return { ...b, todo: addIfAbsent(b.todo, x) };
}
