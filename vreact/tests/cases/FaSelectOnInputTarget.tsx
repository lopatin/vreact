// expect: reject e.target is the element where the event happened
// A select's onInput also runs for an input event a script dispatches at one of its options
// (option.dispatchEvent(new Event("input", { bubbles: true }))): e.target is then the option,
// whose value need not be the select's.  Read e.currentTarget.value (or use onChange: a change
// event at an option makes no onChange).  React types onInput's e.target as an EventTarget, so
// this takes a ChangeEvent annotation (React's handler types are bivariant).
import { useState, type ChangeEvent } from "react";
import { invariant } from "vreact/spec";

export function FaSelectOnInputTarget() {
  const [s, setS] = useState<string>("a");
  invariant(s === "a" || s === "b");
  return (
    <select value={s} onInput={(e: ChangeEvent<HTMLSelectElement>) => {
      const c = e.currentTarget.value;
      if (c === "a" || c === "b") setS(e.target.value);
    }}>
      <option value="a">a</option>
      <option value="b">b</option>
      <option value="zz">zz</option>
    </select>
  );
}
