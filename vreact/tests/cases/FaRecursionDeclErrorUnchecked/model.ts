// expect: status verdict=not-verified errors=internal grow=incomplete failed=0 proved=0 unchecked=1 uncheckedwhy=did~not~elaborate
// An error Lean reports for a declaration at no obligation's marker is the declaration's (a
// translator bug, an environment a proof file changed), never a failure of its only obligation
// (round-2 finding lean-r2-1: the internal error `Unknown identifier …component.node` of a
// self-rendering component was reported as a failed [child-precondition]). Here
// smuggled/Base.lean (a proof file the whitelist rejects, put in place after the translation)
// redefines `≥`, so the statement of grow's postcondition theorem does not elaborate: its
// obligation is not checked (not failed, not proved), the error is listed, NOT VERIFIED.
import { ensures, type int } from "vreact/spec";
export function grow(x: int): int {
  ensures((r: int) => r >= x);
  return x + 1;
}
