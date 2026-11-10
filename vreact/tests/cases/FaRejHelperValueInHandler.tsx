// expect: verified
// A local helper that updates state and returns a value, called in a handler as the
// initializer of a local (`const v = bump();`): its statements run in the handler, in order
// with the handler's own updates, as for the statement `bump();` (formerly rejected as "state
// updates during render"). Also with branches (two returns), a destructured result, a helper
// that calls another updating helper as a statement, and a value-returning helper called as a
// statement (its value is computed and discarded; formerly "event handlers return nothing"),
// and a `useCallback` helper called so in an effect.
import { useCallback, useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  const [log, setLog] = useState<int>(0);
  invariant(n >= 0 && log >= 0 && log <= 10);
  // records the click (log stays within 0..10) and returns the next value of n
  const note = (): void => {
    setLog((l) => (l < 10 ? l + 1 : 10));
  };
  const bump = (): int => {
    note();
    if (n > 5) {
      setLog(0);
      return 0;
    }
    return n + 1;
  };
  const pair = (k: int): readonly [int, int] => {
    setLog((l) => (l > 0 ? l - 1 : 0));
    return [k, k + 1];
  };
  return (
    <div>
      <button onClick={() => { const v = bump(); setN(v); }}>{n}</button>
      <button onClick={() => { const [a, b] = pair(n); setN(b - a + n); }}>+1</button>
      <button onClick={() => { bump(); }}>log</button>
    </div>
  );
}

export function Once() {
  const [n, setN] = useState<int>(0);
  const [runs, setRuns] = useState<int>(0);
  invariant(n >= 0 && runs >= 0);
  const start = useCallback((): int => {
    setRuns((r) => r + 1);
    return 2;
  }, []);
  useEffect(() => {
    const step = start();
    setN((m) => m + step);
  }, [start]);
  return <p>{n}</p>;
}
