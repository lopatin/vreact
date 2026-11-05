// expect: status verdict=not-verified errors=internal bump=incomplete twice=incomplete keep=verified proved=1 unchecked=2
// proofs/Base.lean declares `VTS.model.bump` itself (with a body that satisfies the ensures),
// so the generated `def bump` (whose body violates it) is never added to the environment:
// Lean reports "already declared" and `bump.post`, `twice.post` are proved about the user's
// definition. Neither obligation may count as proved, and twice (which uses bump) must not be
// VERIFIED (before: 2/2 proved, twice=verified; `#print axioms` cannot show the substitution).
import { ensures, type int } from "vreact/spec";
export function bump(x: int): int {
  ensures((r: int) => r > x);
  return x - 1;
}
export function twice(x: int): int {
  ensures((r: int) => r > x + 1);
  return bump(bump(x));
}
export function keep(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
