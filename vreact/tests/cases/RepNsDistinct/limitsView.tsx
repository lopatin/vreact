import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { clampPct } from "./limits";
export function LimitsView() {
  const [pct, setPct] = useState<int>(0);
  invariant(0 <= pct && pct <= 100);
  return <button onClick={() => setPct(clampPct(pct + 60))}>{pct}</button>;
}
