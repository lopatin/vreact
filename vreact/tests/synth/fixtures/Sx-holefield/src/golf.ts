import { ensures, hole, type int } from "vreact/spec";

// a golf score card: a field that happens to be called `hole`
export type Card = { readonly hole: int; readonly strokes: int };

// a parameter that shadows the imported `hole`
export function after(hole: int): int {
  return hole + 1;
}

// once filled, the import of `hole` is unused (noUnusedLocals): the field, the property
// accesses and the parameter above are not uses of it
export function nextHole(c: Card): Card {
  ensures((r: Card) => r.hole === c.hole + 1 && r.strokes === c.strokes);
  return hole<Card>();
}
