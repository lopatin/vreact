import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Cell() {
  const [k, setK] = useState<int>(0);
  invariant(k >= 0);
  return <button onClick={() => setK(k + 1)}>{k}</button>;
}
