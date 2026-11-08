// expect: reject src/RnPureAnnot.tsx:16: the bundler annotation `#__PURE__` is not supported
// A production build (esbuild's minifier, Rollup's tree-shaking) deletes a call annotated as
// pure whose result is unused, with its effects: one click then only increments b, and the
// verified invariant a === b breaks (formerly VERIFIED).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function RnPureAnnot() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a === b);
  return (
    <button
      type="button"
      onClick={() => {
        /* #__PURE__ */ setA(a + 1);
        setB(b + 1);
      }}
    >
      {a}/{b}
    </button>
  );
}
