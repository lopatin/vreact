// expect: reject JSX pragmas (`@jsxImportSource`) are not supported
/** @jsxImportSource ./rt */
// The pragma (a leading comment of the file, which TypeScript honours; Babel and esbuild read
// it in any comment) makes this file's JSX call ./rt/jsx-runtime's jsx, which may do anything
// with an element (e.g. run every button's onClick twice), while VTS models React's.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

const XS: readonly string[] = ["a", "b", "c", "d", "e", "f"];

export function RjJsxPragma() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 5);
  return (
    <div>
      <button onClick={() => { if (n < 5) setN((p) => p + 1); }}>more</button>
      <p>{XS[n].length}</p>
    </div>
  );
}
