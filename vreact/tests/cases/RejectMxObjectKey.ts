// expect: reject by identity
import { type int } from "vreact/spec";

type P = { readonly x: int };
// objects are keys by identity: a copy is another key
export function f(s: ReadonlySet<P>): int {
  return s.size;
}
