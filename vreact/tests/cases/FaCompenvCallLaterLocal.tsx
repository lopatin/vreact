// expect: reject `f` reads `g`, which is declared after it
// `f()` runs in the render before `const g` is initialised (a ReferenceError in JS): rejected,
// now with the true reason (formerly "call to `g` is not supported (only … local helper
// arrows …)", false: `g` is a local helper arrow).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const f = (): int => g();
  const v: int = f();
  const g = (): int => 1;
  return <button onClick={() => setN(n + v)}>{n}</button>;
}
