// expect: reject <input> inside <optgroup>: an <optgroup> may contain only <option> elements
// The same through an <optgroup>: a click on the checkbox in it runs its onClick and the
// select's onChange in one batch.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function FaSelectOptgroupCheckbox() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <select value="x" onChange={() => { if (a + b < 1) setA(a + 1); }}>
      <optgroup label="g">
        <option value="x">x</option>
        <input type="checkbox" onClick={() => { if (a + b < 1) setB(b + 1); }} />
      </optgroup>
    </select>
  );
}
