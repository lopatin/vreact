// Actions and the reducer used by <App/> (useReducer). Reducers must be total:
// React may apply them to any queued state, so they validate their input.
import { ensures, implies, type int } from "vreact/spec";
import { type Board, type ColumnId, wellFormed, keepsCards, addCard, deleteCard, moveCard, setWipLimit } from "./model";

export type Action =
  | { readonly kind: "add"; readonly title: string; readonly points: int }
  | { readonly kind: "move"; readonly id: int; readonly to: ColumnId }
  | { readonly kind: "delete"; readonly id: int }
  | { readonly kind: "setWip"; readonly limit: int };

/** @opaque */
export function boardReducer(b: Board, a: Action): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, a.kind === "delete" ? a.id : null));
  switch (a.kind) {
    case "add":
      return addCard(b, a.title, a.points);
    case "move":
      return moveCard(b, a.id, a.to);
    case "delete":
      return deleteCard(b, a.id);
    case "setWip":
      return setWipLimit(b, a.limit);
  }
}
