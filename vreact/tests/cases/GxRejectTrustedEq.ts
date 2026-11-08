// expect: reject a /** @trusted */ generic function (twoOfThreeEqual<K>) is not supported
// True in JS for every K TypeScript allows (booleans: two of three are equal), but as a Lean axiom
// for every type K with DecidableEq it is false at K := Int, so False would follow.
import { ensures } from "vreact/spec";

/** @trusted */
export function twoOfThreeEqual<K extends boolean>(a: K, b: K, c: K): boolean {
  ensures((r: boolean) => a === b || b === c || a === c);
  return true;
}

export function same3(x: boolean): boolean {
  return twoOfThreeEqual(x, x, x);
}
