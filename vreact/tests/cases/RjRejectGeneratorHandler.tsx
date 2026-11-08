// expect: reject async functions and generators are not supported in VTS
// Calling a generator function does not run its body: this handler does nothing in JS.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjGeneratorHandler() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button type="button" onClick={function* () { setN(n + 1); }}>{n}</button>;
}
