// expect: reject `get` reads `n`, which is declared after it
// The useMemo factory runs at the call: through `get` it reads the state `n` declared after the
// useMemo (a ReferenceError in JS). Formerly VERIFIED.
import { useState, useMemo } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const get = (): int => n;
  const twice = useMemo(() => get() * 2, [get]);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{twice}</button>;
}
