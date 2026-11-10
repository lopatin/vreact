// expect: reject name="createElement" on <iframe>: HTML's named access makes this element the property createElement of the document
// Document is [LegacyOverrideBuiltIns] too, and exposes <iframe>s (their window), <form>s,
// <embed>s and <object>s by name: document.createElement is this frame's window once it is
// rendered, and every element react-dom creates after that (the <p> on the click) throws in its
// render. VERIFIED before.
import { useState } from "react";
import { invariant } from "vreact/spec";
export function Frame() {
  const [open, setOpen] = useState<boolean>(false);
  invariant(open || !open);
  return (
    <div>
      <iframe name="createElement" title="frame" />
      <button type="button" onClick={() => setOpen(true)}>open</button>
      {open && <p>opened</p>}
    </div>
  );
}
