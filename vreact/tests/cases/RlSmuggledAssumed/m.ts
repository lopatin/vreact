// expect: status verdict=not-verified errors=proof sq=incomplete why.sq=kernel~re-check proved=0 unchecked=1
// A proof lemma proved by `VReact.assumed` (backstop of round-2 finding r4-lean-r2-assumed).
// smuggled/m.lean (put in place after the translation: the whitelist rejects the identifier,
// RejectRlAssumed) proves the false `x * x = x + 1` with the library axiom behind `assume(…)`;
// the report said ASSUMES and "✔ VERIFIED modulo assume(…) facts" although the source has no
// assume(). The kernel re-check finds that a declaration of the proof module uses the axiom (only
// generated code may, for the source's assume() sites): Proofs.m and VTS.m.Posts, which imports
// it, are not certified, and sq is INCOMPLETE.
import { ensures, type int } from "vreact/spec";

// false: sq(0) is 0, not 1
export function sq(x: int): int {
  ensures((r: int) => r === x + 1);
  return x * x;
}
