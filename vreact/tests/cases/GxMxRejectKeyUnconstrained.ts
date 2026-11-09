// expect: reject a Map key needs equality: constrain K, e.g. K extends int | string
// A Map key / Set element of a type parameter needs an equality constraint: an unconstrained K
// may be an object (compared by identity) or a number (SameValueZero), unlike Lean equality.
import { type int } from "vreact/spec";

export function hasKey<K, V>(m: ReadonlyMap<K, V>, k: K): boolean {
  return m.has(k);
}
