// expect: reject onClick on a submit button <input>
// type="&#115;ubmit" is "submit": a click on the input also submits its form (onSubmit).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEntitySubmit() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <form onSubmit={(e) => { e.preventDefault(); setN(n + 1); }}>
      <input type="&#115;ubmit" onClick={() => setN(n + 1)} />
    </form>
  );
}
