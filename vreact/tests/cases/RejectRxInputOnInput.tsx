// expect: reject both run on one native "input" event
// One keystroke fires the native `input` event, which React delivers to both
// onInput and onChange of a text input.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Bad() {
  const [edits, setEdits] = useState<int>(0);
  invariant(edits <= 1);
  return <input value="" onInput={() => { if (edits < 1) setEdits((n) => n + 1); }} onChange={() => { if (edits < 1) setEdits((n) => n + 1); }} />;
}
