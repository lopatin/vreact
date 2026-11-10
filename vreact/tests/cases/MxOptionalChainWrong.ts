// expect: fail postcondition
import { ensures, requires, type int } from "vreact/spec";

// wrong: a missing key gives undefined for the whole chain, and ?? then gives true
export function mxocwMissing(m: ReadonlyMap<int, ReadonlySet<int>>, k: int, x: int): boolean {
  requires(!m.has(k));
  ensures((r) => r === false);
  return m.get(k)?.has(x) ?? true;
}
