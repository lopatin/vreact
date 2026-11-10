// expect: fail handler-robust
// Focus handlers are robust.  Clicking "edit" (a trusted click, in Chromium too) renders
// the input; React focuses it during the commit (autoFocus), and the button's onBlur runs
// inside that commit. Focus moves inside other batches like this one (a click on a label
// moves focus to its control, then clicks the control, in one batch when a script
// dispatches the click), so a focus handler is checked from any state, not from its
// snapshot: here n = 1 with the snapshot n = 0 gives 2. Checked from the snapshot, as a
// discrete handler, it was "verified". (The original case had the input's onFocus update
// n as well, in the same batch: a focus handler of an autoFocus element that updates state
// is now rejected, FaDomAutoFocusChain.)
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Edit() {
  const [n, setN] = useState<int>(0);
  const [editing, setEditing] = useState(false);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <button type="button" onClick={() => setEditing(true)} onBlur={() => { if (n < 1) setN((m) => m + 1); }}>edit</button>
      {editing && <input autoFocus />}
    </div>
  );
}
