// expect: reject state `fs` has the function type (x: int) => int, which is not data
// Functions in component state (formerly an internal error).
import { useState } from "react";
import { type int } from "vreact/spec";

export function RnFnState() {
  const [fs, setFs] = useState<readonly ((x: int) => int)[]>([]);
  return <p>{fs.length}</p>;
}
