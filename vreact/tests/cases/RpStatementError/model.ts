// expect: fail postcondition verdict=not-verified errors=internal grow=incomplete keep=verified viaGrow=verified failed=1 proved=2
// proofs/Base.lean redefines `≥` so that the *statement* of grow's postcondition theorem does
// not elaborate (the def bodies do not use `≥`). The obligation must not count as proved
// (its theorem is about an ill-formed statement), grow is INCOMPLETE, the verdict NOT
// VERIFIED; keep and viaGrow (which unfolds grow, not its broken contract) keep their status.
import { ensures, type int } from "vreact/spec";
export function grow(x: int): int {
  ensures((r: int) => r >= x);
  return x + 1;
}
export function keep(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
export function viaGrow(x: int): int {
  ensures((r: int) => r === x + 1);
  return grow(x);
}
