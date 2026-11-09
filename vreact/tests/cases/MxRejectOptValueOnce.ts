// expect: reject Map values must not be optional
// A record type with an optional Map value, used by a function: the error is reported once (it
// was printed twice, from the type's declaration and from its use; the runner checks every
// reject case for duplicates).
import { type int } from "vreact/spec";

export type Ui = { readonly held: ReadonlyMap<int, int | null> };

export function heldOf(u: Ui, id: int): int | null {
  return u.held.get(id) ?? null;
}
