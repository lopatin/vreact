// expect: fail handler
// False control for the board invariant: a handler writes a value outside `[0, 2]`.
/// <reference lib="es2023.array" />
import { useState } from "react";
import { invariant, forall, range, type int } from "vreact/spec";

export function Three() {
  const [cells, setCells] = useState<readonly int[]>([0, 0, 0, 0, 0, 0, 0, 0, 0]);
  invariant(cells.length === 9 && forall(0, 9, (i) => cells[i] >= 0 && cells[i] <= 2));
  return <div>{range(9).map((k) => <button key={k} onClick={() => setCells(cells.with(k, 3))}>{cells[k]}</button>)}</div>;
}
