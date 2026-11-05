// expect: verified
// Layouts whose activation chains reach one discrete handler are accepted
// (react-dom 18.3.1, one programmatic click each): a checkbox / text input / button
// inside a <label> (the label re-dispatches the click to its control, which runs its
// own handler once); a type="button" with onClick in a form with onSubmit; a submit
// button without onClick; onSubmit below the form (the submit event does not reach
// it); a checkbox's onClick + onInput (React renders between click and input: its
// ChangeEventPlugin flushes); <summary onClick> + <details onToggle> (toggle is a
// later task, and robust); onKeyDown in a form (implicit submission follows trusted
// key events only); robust focus handlers, also nested.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  const [on, setOn] = useState(false);
  const [text, setText] = useState<string>("");
  const [focused, setFocused] = useState<int>(0);
  invariant(0 <= n && n <= 1 && text.length <= 10 && focused >= 0);
  return (
    <div>
      <label><input type="checkbox" checked={on} onChange={() => setOn(!on)} /> done</label>
      <label>name <input value={text} onClick={() => { if (n < 1) setN((m) => m + 1); }} onChange={(e) => { if (e.target.value.length <= 10) setText(e.target.value); }} /></label>
      <label><button type="button" onClick={() => setN(0)}>reset</button> counter</label>
      <form onSubmit={(e) => { e.preventDefault(); if (n < 1) setN((m) => m + 1); }}>
        <button type="button" onClick={() => setN(0)}>clear</button>
        <button type="submit">add</button>
        <input onKeyDown={(e) => { if (e.key === "Escape") setText(""); }} />
      </form>
      <form>
        <div onSubmit={() => setN(0)}>
          <button onClick={() => { if (n < 1) setN((m) => m + 1); }}>go</button>
        </div>
      </form>
      <input type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} onInput={() => setN(0)} />
      <details onToggle={() => setFocused((f) => f + 1)}>
        <summary onClick={() => { if (n < 1) setN((m) => m + 1); }}>more</summary>
        details
      </details>
      <div onFocus={() => setFocused((f) => f + 1)}>
        <input onFocus={() => setFocused((f) => f + 1)} onBlur={() => setFocused(0)} />
      </div>
    </div>
  );
}
