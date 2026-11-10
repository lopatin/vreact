// expect: reject name="nodeName" on <output>
// Each value a conditional may give is checked: on the form, nodeName is this <output> when c is
// 1 (and react-dom's ChangeEventPlugin calls form.nodeName.toLowerCase() for an event at the form).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Out() {
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form>
      <output name={c === 0 ? "total" : "nodeName"}>{c}</output>
      <button type="button" onClick={() => setC(1)}>one</button>
    </form>
  );
}
