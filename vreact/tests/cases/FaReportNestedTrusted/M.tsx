// expect: status verdict=verified-modulo-trusted f=relative h=relative c=relative Comp=relative Comp.certificate=relative errors=none
// Attribution by module identity, not by name prefix (audit finding report-r1-1). The nested
// modules M/f.ts, M/c.ts and M/Comp.ts have the Lean namespaces VTS.M.f, VTS.M.c and
// VTS.M.Comp (SEMANTICS §5: namespaces may nest), so their @trusted functions are the axioms
// VTS.M.f.g, VTS.M.c.k and VTS.M.Comp.t — names inside the namespaces of this module's f, c and
// Comp. Before, the report took such an axiom for the item's own @trusted contract: f (but not
// the identical h), c, Comp and its certificate were TRUSTED, "by axioms from outside the
// translation". They rely only on @trusted dependencies: VERIFIED* (relative), like h.
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
import { g } from "./M/f";
import { k } from "./M/c";
import { t } from "./M/Comp";
export function f(x: int): int {
  ensures((r: int) => r > x);
  return g(x);
}
export function h(x: int): int {
  ensures((r: int) => r > x);
  return g(x);
}
export const c: int = k(1);
export function Comp() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  return <button onClick={() => setN(t(n))}>{n}</button>;
}
