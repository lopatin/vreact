import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";
import { clamp } from "./lib";
export function clamp2(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return clamp(x);
}
export function Slider() {
  const [v, setV] = useState<int>(0);
  invariant(0 <= v && v <= 100);
  return <button onClick={() => setV(clamp2(v + 10))}>{v}</button>;
}
