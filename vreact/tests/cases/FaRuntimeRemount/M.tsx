// expect: verified verdict=verified Child=verified App=verified Child.certificate=verified App.certificate=verified errors=none
// attack-1 (runtime): React 18 remounts `<Child key={k} />` when `k` changes, and the `<Child />`
// inside `{wrap ? <div>…</div> : <section>…</section>}` when the host element changes type: fresh
// state, and every effect runs again, as at a mount (here Child's `[]` effect). The model's paths
// contain neither the key outside a list nor the host tag, so `reconcile` kept Child with its
// recorded dependencies and no run of the model (nor `App.certificate`) ever ran the effect again.
// proofs/M.lean proves, of the model, that a run can remount an instance (`Action.remount`):
// initial state, nothing recorded, and the next flush runs the `[]` effect again.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function Child() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  useEffect(() => {
    setN((m) => (m < 10 ? m + 1 : m));
  }, []);
  return <button onClick={() => { if (n < 10) setN(n + 1); }}>{n}</button>;
}

export function App() {
  const [k, setK] = useState<int>(0);
  const [wrap, setWrap] = useState<boolean>(false);
  invariant(0 <= k && k <= 3);
  return (
    <div>
      <button onClick={() => { if (k < 3) setK(k + 1); }}>reset</button>
      <button onClick={() => { setWrap(!wrap); }}>wrap</button>
      <Child key={k} />
      {wrap ? <div><Child /></div> : <section><Child /></section>}
    </div>
  );
}
