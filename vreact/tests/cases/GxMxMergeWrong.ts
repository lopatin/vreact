// expect: fail postcondition
// …but a key of the merge need not be a key of b (it may come from a): still not provable.
import { ensures, type int } from "vreact/spec";

export function mergeWrong(a: ReadonlyMap<int, string>, b: ReadonlyMap<int, string>, k: int): boolean {
  ensures((r: boolean) => !r || b.has(k));
  return new Map([...a, ...b]).has(k);
}
