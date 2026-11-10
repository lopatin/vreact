// expect: reject <input> inside <select>: a <select> may contain only <option> and <optgroup> elements
// The content rule holds wherever the element comes from: here a JSX const rendered under a
// condition inside the select (checked where it is used, as the event-bubbling checks are).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function FaSelectViaConst() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  const extra = <input type="checkbox" onClick={() => { if (a + b < 1) setB(b + 1); }} />;
  return (
    <select value="x" onChange={() => { if (a + b < 1) setA(a + 1); }}>
      <option value="x">x</option>
      {a === 0 && extra}
    </select>
  );
}
