// Shopping cart model: the state, its invariant, and pure operations with contracts.
import { ensures, implies, distinct, type int } from "vreact/spec";

export type Line = { readonly id: int; readonly qty: int };

export const MAX_QTY: int = 9;

/** The invariant: one line per product, and every quantity is 1..9. */
export function wellFormed(lines: readonly Line[]): boolean {
  return distinct(lines, (l) => l.id) && lines.every((l) => 1 <= l.qty && l.qty <= MAX_QTY);
}

/** Add a product (quantity 1), unless it is already in the cart. */
export function add(lines: readonly Line[], id: int): readonly Line[] {
  ensures((r: readonly Line[]) => implies(wellFormed(lines), wellFormed(r)));
  ensures((r: readonly Line[]) => r.some((l) => l.id === id));
  if (lines.some((l) => l.id === id)) return lines;
  return [...lines, { id: id, qty: 1 }];
}

/** Remove a product. Body left for the synthesizer. */
export function remove(lines: readonly Line[], id: int): readonly Line[] {
  ensures((r: readonly Line[]) => implies(wellFormed(lines), wellFormed(r)));
  ensures((r: readonly Line[]) => !r.some((l) => l.id === id));
  ensures((r: readonly Line[]) => lines.every((l) => l.id === id || r.some((m) => m.id === l.id && m.qty === l.qty)));
  return lines.filter((x) => x.id !== id);
}

/** One more of a product (capped at MAX_QTY). */
export function inc(lines: readonly Line[], id: int): readonly Line[] {
  ensures((r: readonly Line[]) => implies(wellFormed(lines), wellFormed(r)));
  return lines.map((l) => (l.id === id && l.qty < MAX_QTY ? { ...l, qty: l.qty + 1 } : l));
}

/** One fewer of a product. */
export function dec(lines: readonly Line[], id: int): readonly Line[] {
  ensures((r: readonly Line[]) => implies(wellFormed(lines), wellFormed(r)));
  return lines.map((l) => (l.id === id && l.qty > 1 ? { ...l, qty: l.qty - 1 } : l));
}
