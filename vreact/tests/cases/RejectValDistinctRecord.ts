// expect: reject distinct (without a key function) on P elements compares object identity
// distinct([p, { ...p }]) is true in JS (a Set compares references): give a key function.
import { distinct, type int } from "vreact/spec";

type P = { readonly x: int };

export function twoCopies(p: P): boolean {
  return distinct([p, { x: p.x }]);
}
