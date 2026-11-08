// expect: fail handler verdict=not-verified Counter=incomplete Counter.certificate=incomplete tick=verified failed=1 errors=none
// smuggled/m.lean (a proof file the whitelist rejects, put in place after the translation)
// adds a simproc to the automation that logs "vreact:ok" whenever it fires, i.e.
// inside the obligations that mention tick. The handler's obligation is false (n = 0 gives -1):
// vreact_ob drops `vreact:` messages logged inside the obligation and reports the failure, so
// the forged evidence never turns it into a proof.
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
