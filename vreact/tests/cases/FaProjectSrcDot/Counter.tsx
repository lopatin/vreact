// expect: verified
// A flat layout ("src": "." in vreact.json) with the default "out", .vreact: "out" may be inside
// "src" (the walk skips directories starting with "."; vreact removes nothing there but Lean files).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./limits";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
