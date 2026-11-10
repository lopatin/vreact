// expect: reject <Opt> inside <select>: a <select> may contain only <option> and <optgroup> elements written in this component
// A user component inside a <select>: its elements are checked as a tree of their own, so
// nothing would hold them to a select's content (here a checkbox).  Inside a select with
// onChange (or an element with handlers around it) this was rejected before; the content rule
// now says it for every select.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Opt() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <input type="checkbox" onClick={() => setN(n + 1)} />;
}

export function FaSelectComponent() {
  return (
    <select defaultValue="x">
      <option value="x">x</option>
      <Opt />
    </select>
  );
}
