// expect: fail postcondition
// …and the fallback is only used for a missing key: a present Set need not contain it.
import { ensures, type int } from "vreact/spec";

export function hasZero(m: ReadonlyMap<int, ReadonlySet<int>>, k: int): boolean {
  ensures((r: boolean) => r);
  return new Set(m.get(k) ?? [0]).has(0);
}
