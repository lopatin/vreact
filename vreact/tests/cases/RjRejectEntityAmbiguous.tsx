// expect: reject the character reference &#+115; is not of the form &#digits; or &#xhex;
// A reference that JSX compilers read differently (esbuild decodes &#+115; as "s",
// TypeScript and Babel keep the text) has no single meaning: rejected.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEntityAmbiguous() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <form onSubmit={(e) => { e.preventDefault(); setN(n + 1); }}>
      <input type="&#+115;ubmit" onClick={() => setN(n + 1)} />
    </form>
  );
}
