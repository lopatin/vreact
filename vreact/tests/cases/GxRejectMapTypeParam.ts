// expect: reject a type parameter inside a Map type (ReadonlyMap<int, T>) is not supported yet
// Merge of generics and Map/Set: type parameters as Map/Set keys, values or elements are not
// supported yet (inference, the instantiation checks and synth do not look inside Map/Set
// types), so they are rejected rather than half-handled.
import { type int } from "vreact/spec";

export function vals<T>(m: ReadonlyMap<int, T>): readonly T[] {
  return [...m.values()];
}
