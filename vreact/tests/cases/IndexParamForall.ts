// expect: verified
// The advised form of a positional condition: forall over the indices.
import { ensures, forall, type int } from "vreact/spec";

export function sameList(a: readonly int[], b: readonly int[]): boolean {
  ensures((r: boolean) => !r || a.length === b.length);
  return a.length === b.length && forall(0, a.length, (i) => a[i] === b[i]);
}

export function copyKeys(m: ReadonlyMap<int, string>): readonly int[] {
  ensures((r: readonly int[]) => r.length === m.size && forall(0, r.length, (i) => r[i] === [...m.keys()][i]));
  return [...m.keys()];
}
