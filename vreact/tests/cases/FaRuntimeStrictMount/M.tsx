// expect: verified verdict=verified App=verified App.certificate=verified errors=none
// attack-1 (runtime): every shipped example mounts its app under `<StrictMode>`. In development,
// React 18.3.1 runs each effect of a newly mounted component a second time in the same flush
// (`commitDoubleInvokeEffectsInDEV`: setup, cleanup, setup, with the same closure), so this
// `[]` effect takes `n` from 0 to 2 with no user event. The docs said the model runs effects "any
// number of times (as React does in StrictMode)", but no run of the model ran an effect a second
// time after mounting. proofs/M.lean proves, of the model, that the first flush can run the effect
// twice (`Action.flush inst rerun true`), and that this happens only at mount.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  useEffect(() => {
    setN((m) => (m < 10 ? m + 1 : m));
  }, []);
  return <button onClick={() => { if (n < 10) setN(n + 1); }}>{n}</button>;
}
