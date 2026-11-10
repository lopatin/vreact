// expect: reject <input> inside <option>: an <option> may contain only text
// A radio button inside an <option>, with no handler of its own: one click on it runs the
// enclosing <div>'s onClick (bubbling) and the select's onChange (ChangeEventPlugin: a click on a
// radio button whose checkedness changed, collected up to the root) in one batch.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function FaSelectOptionRadio() {
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <div onClick={() => { if (a + b < 1) setB(b + 1); }}>
      <select value="x" onChange={() => { if (a + b < 1) setA(a + 1); }}>
        <option value="x">x</option>
        <option value="y"><input type="radio" /></option>
      </select>
    </div>
  );
}
