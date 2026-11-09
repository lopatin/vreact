// expect: verified
// An invariant over a Map's entries ([...m].every(([k, v]) => …)) applies to m.has(k) and to
// [...m.values()] (it proved nothing about them: no lemma linked keys and values to entries).
import { ensures, requires, type int } from "vreact/spec";

export type O = { readonly qty: int };

export function fresh(m: ReadonlyMap<int, O>, next: int): boolean {
  requires([...m].every(([id, o]) => id < next));
  ensures((r: boolean) => r === false);
  return m.has(next);
}

export function grows(m: ReadonlyMap<int, O>, next: int, o: O): int {
  requires([...m].every(([id, p]) => id < next));
  ensures((r: int) => r === m.size + 1);
  return new Map(m).set(next, o).size;
}

export function valuesPositive(m: ReadonlyMap<int, O>): boolean {
  requires([...m].every(([id, o]) => o.qty > 0));
  ensures((r: boolean) => r);
  return [...m.values()].every((o) => o.qty > 0);
}
