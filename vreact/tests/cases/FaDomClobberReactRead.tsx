// expect: reject name="correspondingUseElement" on <input>
// No browser defines form.correspondingUseElement, but react-dom reads it on every event's
// target (getEventTarget): a submit event (target: the form) would be dispatched as if its target
// were this <input>. Names react-dom reads on a node that may be a form count too.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Send() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <form onSubmit={() => setN(n + 1)}>
      <input name="correspondingUseElement" />
      <p>{n}</p>
    </form>
  );
}
