import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "../model";

export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + 1); }}>{n}</button>;
}
