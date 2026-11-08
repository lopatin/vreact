// expect: reject the initialiser of `A` calls `g`, which reads `B`, declared below it
// JS evaluates module constants in order: A's initialiser calls g, which reads B before B's
// declaration has run, so loading the module throws a ReferenceError (TypeScript only flags
// direct reads). Formerly translated in dependency order and h's contract proved.
import { type int, ensures } from "vreact/spec";

function g(): int {
  return B;
}
export const A: int = g() + 1;
export const B: int = 2;

export function h(): int {
  ensures((r) => r === 3);
  return A;
}
