// expect: fail handler verdict=not-verified Counter=incomplete Counter.certificate=incomplete tick=verified failed=1 errors=proof
// smuggled/m.lean (a proof file the whitelist rejects, put in place after the translation)
// adds a simproc to the automation that logs "vreact:ok" whenever it fires, i.e.
// inside the obligations that mention tick. The handler's obligation is false (n = 0 gives -1):
// vreact_ob drops `vreact:` messages logged inside the obligation and reports the failure, so
// the forged evidence never turns it into a proof.
// Round 2 (r4-lean-r2): the kernel re-check of the built modules finds the simproc in Proofs.m
// (a proof module may add theorems, definitions and simp/grind attributes only): an error of the
// user proofs (the old expectation `errors=none` described a report that did not notice the
// smuggled simproc), and Counter's View, which imports Proofs.m, is not certified; tick (in Defs,
// which does not import it) stays VERIFIED.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function tick(x: int): int {
  return x - 1;
}
export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(tick(n))}>{n}</button>;
}
