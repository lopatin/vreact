// expect: verified verdict=verified App=verified App.certificate=verified errors=none
// lean-r1-2: React 18 re-runs an effect when a dependency changed since the previous render
// (`Object.is` per dependency): here, cleanup and a new interval with the new `step` on every
// change of `step`. The runtime model compared an effect's dependencies with themselves, so
// `run` (and so `App.certificate`) never re-ran an effect that has a dependency array.
// proofs/M.lean proves, of the model, that the effect runs again (and registers its timers)
// once a dependency changed, and not when none did.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [step, setStep] = useState<int>(1);
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 100 && 1 <= step && step <= 5);
  useEffect(() => {
    const id = setInterval(() => setN((m) => (m + step <= 100 ? m + step : m)), 1000);
    return () => { clearInterval(id); };
  }, [step]);
  return <button onClick={() => { if (step < 5) setStep(step + 1); }}>{n}</button>;
}
