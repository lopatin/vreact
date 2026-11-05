// expect: verified
// Conditional effects (`if (!running) return;`) and conditional continuous
// handlers (if, loop, switch): their emit-freedom is proved by the translator's
// own tactic (it used to be `rfl`, which fails on an `if`).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
type Mode = "up" | "down";
export function Ticker() {
  const [running, setRunning] = useState(false);
  const [n, setN] = useState<int>(0);
  const [seen, setSeen] = useState(false);
  const [mode, setMode] = useState<Mode>("up");
  invariant(n >= 0);
  useEffect(() => {
    if (!running) return;
    const id = setInterval(() => setN((m) => m + 1), 1000);
    return () => clearInterval(id);
  }, [running]);
  const steps: readonly int[] = [1, 2];
  return (
    <div
      onScroll={() => { if (!seen) setSeen(true); }}
      onWheel={() => {
        let s: int = 0;
        for (const x of steps) s = s + x;
        switch (mode) {
          case "up":
            setN((m) => m + s);
            break;
          case "down":
            setN((m) => (m >= s ? m - s : m));
            break;
        }
      }}
    >
      <button onClick={() => setRunning(!running)}>{n}</button>
      <button onDoubleClick={() => setMode(mode === "up" ? "down" : "up")}>{mode}</button>
    </div>
  );
}
