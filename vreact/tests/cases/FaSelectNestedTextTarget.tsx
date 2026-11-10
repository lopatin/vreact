// expect: reject <input> inside <select>: a <select> may contain only <option> and <optgroup> elements
// A text field inside a <select onChange>: typing "zz" in it fires input at the field, which
// ChangeEventPlugin turns into an onChange collected up to the select, with e.target the field
// and e.currentTarget the select, so the model's one value for both is wrong: s becomes "zz".
import { useState } from "react";
import { invariant } from "vreact/spec";

export function FaSelectNestedTextTarget() {
  const [s, setS] = useState<string>("a");
  invariant(s === "a" || s === "b");
  return (
    <select value={s} onChange={(e) => {
      const c = e.currentTarget.value;
      if (c === "a" || c === "b") setS(e.target.value);
    }}>
      <option value="a">a</option>
      <option value="b">b</option>
      <input defaultValue="" />
    </select>
  );
}
