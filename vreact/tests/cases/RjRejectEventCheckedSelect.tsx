// expect: reject only an <input> has checked
// A change handler whose event type claims a `checked` (a subtype of the select's event
// type, so the bivariant handler types accept it) on a <select>: its target is the select,
// which has no `checked` (undefined, not a boolean).
import { useState, type ChangeEvent } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEventCheckedSelect() {
  const [on, setOn] = useState<boolean>(false);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <select value="a" onChange={(e: ChangeEvent<HTMLSelectElement & { readonly checked: boolean }>) => setOn(e.target.checked)}>
        <option value="a">a</option>
      </select>
      <button type="button" onClick={() => setN(on ? n + 1 : n)}>{n}</button>
    </div>
  );
}
