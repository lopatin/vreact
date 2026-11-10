// expect: reject useState(…) as a statement (its value unused) is not supported
// A hook called as a statement at the top level with its value unused: rejected for what it is,
// not for a Rules of Hooks violation.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useState<int>(1);
  return <button onClick={() => setN(0)}>{n}</button>;
}
