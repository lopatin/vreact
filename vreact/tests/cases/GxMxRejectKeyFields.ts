// expect: reject a Map key needs equality: the type parameter T has a field constraint
// A field-constrained type parameter is instantiated with records, which a JS Map compares by
// identity (a copy is a different key): key by a field instead.
import { type int } from "vreact/spec";

export function seen<T extends { readonly id: int }>(m: ReadonlyMap<T, boolean>, x: T): boolean {
  return m.has(x);
}
