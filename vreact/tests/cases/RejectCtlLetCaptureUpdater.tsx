// expect: reject which is reassigned after the function is created
// React may call the functional update later (during the next render), when step === 50.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlHandlerLet() {
  const [n, setN] = useState<int>(0);
  const [tick, setTick] = useState<int>(0);
  invariant(0 <= n && n <= 10 && 0 <= tick);
  return (
    <button
      onClick={() => {
        setTick(tick + 1);
        let step: int = 1;
        setN((m) => (m < 10 ? m + step : m));
        step = 50;
      }}
    >
      {n}
    </button>
  );
}
