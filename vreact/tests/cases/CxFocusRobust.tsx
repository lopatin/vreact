// expect: fail handler-robust
// Focus handlers are robust.  Clicking "edit" (a trusted click, in Chromium too) renders
// the input; React focuses it during the commit (autoFocus): the button's onBlur and
// the input's onFocus run in one batch, both from the snapshot n = 0, and n becomes 2.
// Checked from the snapshot, as discrete handlers, both were "verified".
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Edit() {
  const [n, setN] = useState<int>(0);
  const [editing, setEditing] = useState(false);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <button type="button" onClick={() => setEditing(true)} onBlur={() => { if (n < 1) setN((m) => m + 1); }}>edit</button>
      {editing && <input autoFocus onFocus={() => { if (n < 1) setN((m) => m + 1); }} />}
    </div>
  );
}
