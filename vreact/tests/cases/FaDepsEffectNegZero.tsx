// expect: verified FaDepsEffectNegZero=verified
// An int dependency that switches between 0 and -0 (`k` is -0 while n is 0): React's `Object.is`
// tells them apart, so React re-creates `bump` and runs the effect again, while the model compares
// the ints as integers (0 = 0) and does not. SEMANTICS §2.6 documents this departure (it said the
// model's dependency values follow React's identities exactly, and that the effect runs at least
// as often as in React): it changes nothing verified, because the effect, like every effect, keeps
// the invariant from any valid state, whichever render's effect runs.
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsEffectNegZero() {
  const [n, setN] = useState<int>(3);
  const [runs, setRuns] = useState<int>(0);
  invariant(runs >= 0);
  const k: int = n > 0 ? 0 : -n;
  const bump = useCallback(() => setRuns((p) => p + 1), [k]);
  useEffect(() => {
    bump();
  }, [bump]);
  useEffect(() => {
    setRuns((p) => (p >= 0 ? p + 1 : 0));
  }, [k]);
  return (
    <button type="button" onClick={() => setN(n > 0 ? 0 : 3)}>
      {runs}
    </button>
  );
}
