// expect: reject one native "click" event would run both (event bubbling)
// A clickable row around a checkbox: the checkbox's onChange (fired by the native
// click) and the row's onClick (the same click, bubbling) run in one batch.
import { useState } from "react";
import { invariant } from "vreact/spec";
export function Bad() {
  const [insurance, setInsurance] = useState(false);
  const [priority, setPriority] = useState(false);
  invariant(!(insurance && priority));
  return (
    <ul>
      <li onClick={() => { if (!insurance) setPriority(true); }}>
        <input type="checkbox" checked={insurance} onChange={() => { if (!priority) setInsurance(!insurance); }} />
      </li>
    </ul>
  );
}
