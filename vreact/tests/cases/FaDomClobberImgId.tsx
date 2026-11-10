// expect: reject id="parentNode" on <img>
// A form's named getter answers by the ids (and names) of the images in it as well: form.parentNode
// is this <img>, whose parentNode is the form, and react-dom's radio-group restore loops forever
// after a click on a radio button. VERIFIED before.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Pick() {
  const [c, setC] = useState<int>(0);
  invariant(c >= 0 && c <= 1);
  return (
    <form>
      <img id="parentNode" src="flag.png" alt="flag" />
      <input type="radio" name="size" checked={c === 0} onChange={() => setC(0)} />
      <input type="radio" name="size" checked={c === 1} onChange={() => setC(1)} />
    </form>
  );
}
