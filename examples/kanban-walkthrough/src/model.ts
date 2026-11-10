// The board model: data, its well-formedness invariant, and total operations
// that provably preserve it.
import { ensures, implies, distinct, type int } from "vreact/spec";

export type ColumnId = "todo" | "doing" | "done";
export type Card = { readonly id: int; readonly title: string; readonly points: int };
export type Board = {
  readonly todo: readonly Card[];
  readonly doing: readonly Card[];
  readonly done: readonly Card[];
  readonly nextId: int;
  readonly wipLimit: int;
};

export const MAX_TITLE = 60;
export const MAX_POINTS = 13;

export function validTitle(t: string): boolean {
  return t.length > 0 && t.length <= MAX_TITLE;
}

export function validPoints(p: int): boolean {
  return 1 <= p && p <= MAX_POINTS;
}

export function allCards(b: Board): readonly Card[] {
  return [...b.todo, ...b.doing, ...b.done];
}

/** The board invariant: unique ids below nextId, valid cards, WIP limit respected. */
export function wellFormed(b: Board): boolean {
  const cards = allCards(b);
  return (
    distinct(cards, (c) => c.id) &&
    cards.every((c) => c.id < b.nextId && validTitle(c.title) && validPoints(c.points)) &&
    b.wipLimit >= 1 &&
    b.doing.length <= b.wipLimit
  );
}

export function cardsIn(b: Board, col: ColumnId): readonly Card[] {
  switch (col) {
    case "todo":
      return b.todo;
    case "doing":
      return b.doing;
    case "done":
      return b.done;
  }
}

export function findCard(b: Board, id: int): Card | null {
  return allCards(b).find((c) => c.id === id) ?? null;
}

/** Every card of `b` — except the one with id `except`, if any — is still on `r`. */
export function keepsCards(b: Board, r: Board, except: int | null): boolean {
  return allCards(b).every((c) => (except !== null && c.id === except) || allCards(r).some((d) => d.id === c.id));
}

export function removeEverywhere(b: Board, id: int): Board {
  return {
    ...b,
    todo: b.todo.filter((c) => c.id !== id),
    doing: b.doing.filter((c) => c.id !== id),
    done: b.done.filter((c) => c.id !== id),
  };
}

/** @opaque */
export function addCard(b: Board, title: string, points: int): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, null));
  ensures((r: Board) => implies(validTitle(title) && validPoints(points), r.todo.some((c) => c.title === title && c.points === points)));
  if (!validTitle(title) || !validPoints(points)) return b;
  return { ...b, todo: [...b.todo, { id: b.nextId, title, points }], nextId: b.nextId + 1 };
}

/** @opaque */
export function deleteCard(b: Board, id: int): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, id));
  ensures((r: Board) => allCards(r).every((c) => c.id !== id));
  return removeEverywhere(b, id);
}

/** @opaque */
export function moveCard(b: Board, id: int, to: ColumnId): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, null));
  ensures((r: Board) => implies(findCard(b, id) !== null && (to !== "doing" || b.doing.length < b.wipLimit), cardsIn(r, to).some((c) => c.id === id)));
  const card = findCard(b, id);
  if (card === null) return b;
  const rest = removeEverywhere(b, id);
  switch (to) {
    case "todo":
      return { ...rest, todo: [...rest.todo, card] };
    case "doing":
      if (rest.doing.length >= b.wipLimit) return b;
      return { ...rest, doing: [...rest.doing, card] };
    case "done":
      return { ...rest, done: [...rest.done, card] };
  }
}

/** @opaque */
export function setWipLimit(b: Board, limit: int): Board {
  ensures((r: Board) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Board) => keepsCards(b, r, null));
  ensures((r: Board) => implies(limit >= 1 && limit >= b.doing.length, r.wipLimit === limit));
  if (limit < 1 || limit < b.doing.length) return b;
  return { ...b, wipLimit: limit };
}

export const initialBoard: Board = {
  todo: [
    { id: 1, title: "Write the spec", points: 3 },
    { id: 2, title: "Synthesize the model", points: 5 },
  ],
  doing: [{ id: 3, title: "Verify the components", points: 8 }],
  done: [],
  nextId: 4,
  wipLimit: 2,
};
