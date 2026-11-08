// expect: reject state `fs` has the function type (x: int) => int, which is not data
// Component state holding functions has no Lean value type (it crashed the translator before).
import { useState } from "react";
import { type int } from "vreact/spec";

export function Funcs() {
  const [fs, setFs] = useState<readonly ((x: int) => int)[]>([]);
  return <p>{fs.length}</p>;
}
