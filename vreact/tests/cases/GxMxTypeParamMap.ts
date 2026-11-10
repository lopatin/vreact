// expect: verified vals=verified
// Formerly GxRejectMapTypeParam: a type parameter inside a Map type was rejected before generics
// and Map/Set were integrated. A Map value may be any type parameter (here unconstrained T).
import { ensures, type int } from "vreact/spec";

export function vals<T>(m: ReadonlyMap<int, T>): readonly T[] {
  ensures((r: readonly T[]) => r.length === m.size);
  return [...m.values()];
}
