// expect: reject <input> inside <select>: a <select> may contain only <option> and <optgroup> elements
// A checkbox inside a <select onChange>: react-dom's ChangeEventPlugin picks the native event by
// the target control (a click on a checkbox) and collects onChange on the whole path to the root,
// so one click runs the checkbox's onClick and the select's onChange in one batch, from one
// snapshot: a = b = 1 breaks the invariant.  React only warns about the nesting.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function FaSelectNestedCheckbox() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <select value="x" onChange={() => { if (a + b < 1) setA(a + 1); }}>
      <option value="x">x</option>
      <input type="checkbox" onClick={() => { if (a + b < 1) setB(b + 1); }} />
    </select>
  );
}
