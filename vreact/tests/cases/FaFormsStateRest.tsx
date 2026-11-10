// expect: reject a rest element in the destructuring of useState(…) is not supported
// JS binds rest to the pair [0, setter]; the model treated it as the int state (VERIFIED).
import { useState } from "react";
import { int, invariant } from "vreact/spec";

export function C() {
  const [...rest] = useState<int>(0);
  invariant(String(rest) === "0");
  return <p>{String(rest)}</p>;
}
