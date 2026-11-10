// expect: reject which is reassigned after the function is created
// The effect (and its timer) run after render, when step === 100.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlEffectLet() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let step: int = 1;
  useEffect(() => {
    const id = setInterval(() => setN((m) => (m < 10 ? m + step : m)), 1000);
    return () => clearInterval(id);
  }, [step]);
  step = 100;
  return <p>{n}</p>;
}
