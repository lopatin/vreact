import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { Cell } from "./ui/Board";
export function Board() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <div><Cell /><button onClick={() => setN(n + 1)}>{n}</button></div>;
}
