// expect: fail postcondition verdict=not-verified clamp=incomplete clamp2=incomplete safe=verified Counter=verified Counter.certificate=verified Panel=verified failed=1 unchecked=0 errors=none why.clamp=obligation~of~it~failed why.clamp2=uses~clamp~(src/lib.tsx)
// A failing obligation is a warning (vreact_ob admits its goal with sorry), not a Lean error:
// the module's View.lean and the modules importing it are still built and checked (before: the
// failing clamp.post in Defs.lean kept lake from building lib's View and use's Defs, so Counter,
// Panel, clamp2 and safe were UNCHECKED). clamp2's own obligation is proved, but it relies on
// clamp's failed contract (sorryAx): INCOMPLETE, and the report names clamp as the reason.
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
/** @opaque */
export function clamp(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return x < 0 ? 0 : x;
}
export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
