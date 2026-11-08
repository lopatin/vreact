// expect: status verdict=not-verified errors=internal bump=incomplete twice=incomplete keep=incomplete why.keep=kernel~re-check proved=0 unchecked=3
// smuggled/Base.lean (a proof file the whitelist rejects, put in place after the translation)
// declares `VTS.model.bump` itself (with a body that satisfies the ensures),
// so the generated `def bump` (whose body violates it) is never added to the environment:
// Lean reports "already declared" and `bump.post`, `twice.post` are proved about the user's
// definition. Neither obligation may count as proved, and twice (which uses bump) must not be
// VERIFIED (before: 2/2 proved, twice=verified; `#print axioms` cannot show the substitution).
// Round 2 (r4-lean-r2): the kernel re-check finds the definition `VTS.model.bump` in Proofs.Base;
// every module importing it is not certified, so keep (VERIFIED before: the old expectation was
// wrong) is not either — it was elaborated after a user proof that changed the environment.
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
