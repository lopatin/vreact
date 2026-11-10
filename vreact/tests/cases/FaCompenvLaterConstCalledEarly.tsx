// expect: reject `total` reads `step`, which is declared after it
// Calling the closure during the render before `const step` has run reads `step` in its temporal
// dead zone (a ReferenceError in JS): still rejected, now with a true reason (formerly "unknown or
// unsupported identifier `step` (only locals, … can be referenced)").
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const total = (): int => n + step;
  const shown: int = total();
  const step: int = 2;
  return <button onClick={() => setN(n + step)}>{shown}</button>;
}
