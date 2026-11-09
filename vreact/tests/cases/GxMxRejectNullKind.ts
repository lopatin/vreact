// expect: reject null and undefined are different JS values, and the generic function was checked for the one its parameter type names
// TypeScript absorbs `undefined` into V (V = number | undefined) for a Map whose values hold
// `int | undefined` where the parameter says `V | null`: the body's `x === null` would not see
// those `undefined`s. The nullish kinds inside Map values must be the declared ones.
import { type int } from "vreact/spec";

export function firstIsNull<V>(m: ReadonlyMap<int, readonly (V | null)[]>, k: int): boolean {
  const xs = m.get(k);
  if (xs === undefined) return false;
  return xs.length > 0 && xs[0] === null;
}

export function check(m: ReadonlyMap<int, readonly (int | undefined)[]>): boolean {
  return firstIsNull(m, 1);
}
