// expect: reject name="querySelectorAll" on <form>: HTML's named access makes this element the property querySelectorAll of the document
// document.querySelectorAll is this form: react-dom's radio-group restore calls it on the document
// (updateNamedCousins walks up to it) after every click on a controlled radio button, and throws.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Pick() {
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form name="querySelectorAll">
      <input type="radio" name="size" checked={c === 0} onChange={() => setC(0)} />
      <input type="radio" name="size" checked={c === 1} onChange={() => setC(1)} />
    </form>
  );
}
