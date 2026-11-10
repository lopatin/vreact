// expect: reject Tuple type '[number, string]' of length '2' has no element at index '2'
// A pattern longer than the tuple: JS binds undefined to the extra names (TypeScript rejects it;
// so does the translator). (A shorter one binds
// a prefix, exactly as JS: MxTuplePrefix; this case rejected `([k]) => k` before.)
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, string>): readonly int[] {
  return [...m.entries()].map(([k, v, w]) => k);
}
