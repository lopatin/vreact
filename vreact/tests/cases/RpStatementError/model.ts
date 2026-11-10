// expect: status verdict=not-verified errors=internal grow=incomplete keep=incomplete viaGrow=incomplete why.keep=kernel~re-check failed=0 proved=0 unchecked=3
// smuggled/Base.lean (a proof file the whitelist rejects, put in place after the translation)
// redefines `≥` so that the *statement* of grow's postcondition theorem does
// not elaborate (the def bodies do not use `≥`). The obligation must not count as proved
// (its theorem is about an ill-formed statement), grow is INCOMPLETE, the verdict NOT
// VERIFIED; keep and viaGrow (which unfolds grow, not its broken contract) keep their status.
// Round 2 (lean-r2-1): the statement's error is the declaration's, not a failure of its only
// obligation: that obligation is not checked (it was reported as a failed postcondition).
// Round 2 (r4-lean-r2): the kernel re-check finds the macro in Proofs.Base; every module
// importing it is not certified, so keep and viaGrow (VERIFIED before: the old expectation was
// wrong) are not either — they were elaborated with a user proof's macro in effect.
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
