// expect: status verdict=verified-modulo-trusted gα=trusted f=relative Bα=trusted Bα.certificate=trusted Shell=relative Shell.certificate=relative errors=none
// @trusted axioms are matched by Lean name, not by spelling (attack on the fix of report-r1-1):
// the translator writes the @trusted function gα as VTS.App.«gα» (it escapes every non-ASCII
// name), but `#print axioms` prints VTS.App.gα (α is a Lean letter), so gα's axioms counted as
// declared outside the translation: f, Shell and its certificate were TRUSTED "by axioms from
// outside the translation (in a user proof)", in a project without user proofs. They rely only
// on the @trusted gα and Bα: VERIFIED* (relative), as with ASCII names.
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
/** @trusted */
export function gα(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
export function f(x: int): int {
  ensures((r: int) => r > x);
  return gα(x);
}
/** @trusted */
export function Bα() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
export function Shell() {
  return <div><Bα /></div>;
}
