// expect: reject the initialiser of `A` calls `g`, which reads `B`, declared below it
// The name of a shorthand property `{ B }` reads the variable B: A's initialiser calls g, which
// evaluates `{ B }` while B is still in its temporal dead zone, so loading the module throws a
// ReferenceError. Formerly VERIFIED: the init-order check resolved `B` to the object literal's
// property, not to the constant (`two` makes the Lean declaration order put B before g).
import { type int, ensures } from "vreact/spec";

type P = { readonly B: int };
export function two(): int {
  return B;
}
function g(): P {
  return { B };
}
export const A: P = g();
export const B: int = 2;

export function h(): int {
  ensures((r) => r === 2);
  return A.B;
}
