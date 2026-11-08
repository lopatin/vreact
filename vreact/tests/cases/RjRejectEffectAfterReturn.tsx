// expect: reject unreachable code after return
// JS never runs what follows the effect's `return`: setB is not called, so a = b breaks.
// (The model used to apply both updates.)
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEffectAfterReturn() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a === b);
  useEffect(() => {
    setA((x) => x + 1);
    return;
    setB((x) => x + 1);
  }, []);
  return <p>{a} {b}</p>;
}
