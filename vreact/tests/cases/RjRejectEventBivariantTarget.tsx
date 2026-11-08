// expect: reject e.target is the element where the event happened
// A change handler typed for an <input> on a <div>, passed by name: the change event that
// reaches it may come from the <select> (no `checked`: undefined) or from the text input.
import { useState, type ChangeEvent } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEventBivariantTarget() {
  const [on, setOn] = useState<boolean>(false);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const onToggle = (e: ChangeEvent<HTMLInputElement>) => {
    setOn(e.target.checked);
    setN(on ? n + 1 : n);
  };
  return (
    <div onChange={onToggle}>
      <select value="a">
        <option value="a">a</option>
        <option value="b">b</option>
      </select>
      <input type="checkbox" />
      <p>{on ? "on" : "off"} {n}</p>
    </div>
  );
}
