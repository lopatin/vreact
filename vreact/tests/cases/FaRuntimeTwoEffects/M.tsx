// expect: verified verdict=verified App=verified App.certificate=verified errors=none
// attack-1 (runtime): React 18 compares each effect's dependencies with the ones the previous
// render gave *that* effect (by hook order). The fix of lean-r1-2 chose them by index, but every
// fact about it (library and FaRuntimeEffectRerun) was about one-effect components, so a model
// that compared every effect with effect 0's recorded array still built and passed. Here `a` and
// `b` change independently; proofs/M.lean proves, of the model, that a flush runs exactly the
// effects whose own dependency changed (with effect 0's array, the second effect would also run).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [a, setA] = useState<int>(1);
  const [b, setB] = useState<int>(5);
  const [n, setN] = useState<int>(0);
  const [m, setM] = useState<int>(0);
  invariant(1 <= a && a <= 9 && 1 <= b && b <= 9 && 0 <= n && n <= 100 && 0 <= m && m <= 100);
  useEffect(() => {
    setN((x) => (x < 100 ? x + 1 : x));
  }, [a]);
  useEffect(() => {
    setM((x) => (x < 100 ? x + 1 : x));
  }, [b]);
  return (
    <div>
      <button onClick={() => { if (a < 9) setA(a + 1); }}>{n}</button>
      <button onClick={() => { if (b < 9) setB(b + 1); }}>{m}</button>
    </div>
  );
}
