// expect: status verdict=verified-modulo-trusted Badge=trusted Badge.certificate=trusted Shell=relative Shell.certificate=relative errors=none
// A @trusted component's certificate takes the component's own @trusted axioms (its root
// component's, by name: cli.ts `items`), so it is TRUSTED, and a component that renders it is
// VERIFIED* (relative), as is its certificate. Pins the attribution the fix of report-r1-1
// rewrote: if the root lookup missed, Badge.certificate would drop to VERIFIED* unnoticed.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
/** @trusted */
export function Badge() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
export function Shell() {
  return <div><Badge /></div>;
}
