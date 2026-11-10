// expect: fail handler
// A handler created before the useState it reads and attached after it is translated where it
// is attached, with that render's state: it is checked, and this one breaks the invariant.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const dec = () => setN(n - 1);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={dec}>{n}</button>;
}
