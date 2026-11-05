import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
import { clamp, Counter } from "./lib";
export function clamp2(x: int): int {
  ensures((r: int) => r <= 100);
  return clamp(x);
}
export function safe(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
export function Panel() {
  const [k, setK] = useState<int>(1);
  invariant(k > 0);
  return (
    <div>
      <Counter />
      <button onClick={() => setK(safe(k))}>{k}</button>
    </div>
  );
}
