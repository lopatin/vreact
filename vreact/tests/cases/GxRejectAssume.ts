// expect: reject assume(…) is not supported in a generic function (twoOfThreeEqual<K>)
// The assumed fact is true for every call TypeScript allows (K is a boolean type: of three
// values two are equal), but Lean keeps an assumed fact as a theorem about the function's
// parameters (`twoOfThreeEqual._proof_1`, which a user proof can name), here for every Lean type
// K with decidable equality — false at K := Int, so a user proof could derive False from it
// without naming VReact.assumed. Rejected, as @trusted generics are: requires(…) instead.
import { ensures, assume } from "vreact/spec";

export function twoOfThreeEqual<K extends boolean>(a: K, b: K, c: K): boolean {
  ensures((r: boolean) => r);
  assume(a === b || b === c || a === c);
  return a === b || b === c || a === c;
}

export function same3(x: boolean): boolean {
  return twoOfThreeEqual(x, x, x);
}
