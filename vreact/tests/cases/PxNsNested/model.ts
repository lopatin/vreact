// expect: verified verdict=verified count=verified Board=verified Board.certificate=verified errors=none
// Module namespaces may nest when no Lean names collide: the component Board of src/ui.tsx
// (VTS.ui.Board.Props, …) next to the module src/ui/Board.tsx (its component Cell is
// VTS.ui.Board.Cell.Props, …), and the type todo of src/model.ts (VTS.model.todo, with its
// fields and constructor) next to the module src/model/todo.ts (VTS.model.todo.nextId). Before:
// both rejected as a "Lean name clash" although they verified on 95e1756.
import { ensures, type int } from "vreact/spec";
export type todo = { readonly id: int; readonly done: boolean };
export function count(xs: readonly todo[]): int {
  ensures((r: int) => r >= 0);
  return xs.length;
}
