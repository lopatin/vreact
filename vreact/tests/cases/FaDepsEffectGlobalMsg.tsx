// expect: reject `Math` is declared outside the component, and not a top-level declaration of the program
// A global (`Math`) is not a top-level declaration of the program, and the dependency check never
// requires one: as an effect dependency, also through a useCallback that lists it, it is refused
// with that reason (a global need not keep its value: `innerWidth` changes). Before: "a function
// value can only be called, or used as an event handler / callback" at the effect's `[cb]`.
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsEffectGlobalMsg() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const cb = useCallback(() => setN((p) => Math.max(p, 0)), [Math]);
  useEffect(() => {
    cb();
  }, [cb]);
  return <p>{n}</p>;
}
