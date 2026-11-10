// expect: reject src/RnNoSideEffects.tsx:12: the bundler annotation `@__NO_SIDE_EFFECTS__` is not supported
// A function annotated as free of side effects: production builds delete its calls whose
// result is unused (`bump();` below), so a click only increments b (formerly VERIFIED with
// the invariant a === b).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function RnNoSideEffects() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a === b);
  const bump = /* @__NO_SIDE_EFFECTS__ */ () => {
    setA(a + 1);
  };
  return (
    <button
      type="button"
      onClick={() => {
        bump();
        setB(b + 1);
      }}
    >
      {a}/{b}
    </button>
  );
}
