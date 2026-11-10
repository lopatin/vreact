// expect: status verdict=incomplete Comp=verified Comp.certificate=verified errors=none
// A component owns the declarations of its own module in its namespace, not those of a module
// nested there (audit finding report-r1-2): M/Comp.ts (namespace VTS.M.Comp) has a function k
// with a hole(), whose `sorry` warning (declaration VTS.M.Comp.k.post) the report used to count
// as Comp's own — Comp was INCOMPLETE "pending: it has a hole() / sorry" with all its
// obligations proved and clean axioms. Only k is pending (the verdict stays INCOMPLETE).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Comp() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
