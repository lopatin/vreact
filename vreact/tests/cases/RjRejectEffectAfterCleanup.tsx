// expect: reject unreachable code after return
// Also after `return cleanup`: the statements after it never run.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEffectAfterCleanup() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a === b);
  useEffect(() => {
    setA((x) => x + 1);
    return () => console.log("bye");
    setB((x) => x + 1);
  }, []);
  return <p>{a} {b}</p>;
}
