// expect: reject name="parentNode" on <input>: HTML's named access makes this element the property parentNode of the form
// runtime-r2-3: HTMLFormElement is [LegacyOverrideBuiltIns]: form.parentNode is the <input>,
// whose parentNode is the form. A click on a controlled radio button makes react-dom 18.3.1
// restore the group (updateNamedCousins), which walks `while (queryRoot.parentNode)` up from
// the radio button: it never ends, and the page freezes inside the click. VERIFIED before.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function Pick() {
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form>
      <input type="radio" name="size" checked={c === 0} onChange={() => setC(0)} />
      <input type="radio" name="size" checked={c === 1} onChange={() => setC(1)} />
      <input name="parentNode" />
      <p>{c}</p>
    </form>
  );
}
