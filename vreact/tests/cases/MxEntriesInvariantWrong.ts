// expect: fail postcondition
// An id bound over the entries says nothing about which ids are present.
import { ensures, requires, type int } from "vreact/spec";

export type O2 = { readonly qty: int };

export function present(m: ReadonlyMap<int, O2>, next: int): boolean {
  requires([...m].every(([id, o]) => id < next));
  ensures((r: boolean) => r);
  return m.has(next - 1);
}
