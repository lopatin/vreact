import { ensures, implies, distinct, hole, type int } from "vreact/spec";

export type Board = { readonly todo: readonly int[]; readonly done: readonly int[] };

// a helper with its own contract: its postconditions are about its own result, not addTodo's
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
  return hole<Board>();
}
