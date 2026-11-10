// expect: reject every callbacks take only the element in VTS (an index parameter is supported for map only
// An index parameter of every(): the message says what to write (it said "unexpected extra lambda
// parameter"); the forall form is in IndexParamForall.
import { type int } from "vreact/spec";

export function sameList(a: readonly int[], b: readonly int[]): boolean {
  return a.length === b.length && a.every((x, i) => b[i] === x);
}
