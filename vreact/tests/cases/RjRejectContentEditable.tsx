// expect: reject contentEditable is not supported
// With contentEditable the user can delete the <b> React rendered (select it, Backspace); when
// `on` turns false React calls div.removeChild(b), which throws NotFoundError, and the app
// unmounts. The model's tree assumes React owns the DOM under the element.
import { useState } from "react";

export function RjContentEditable() {
  const [on, setOn] = useState(true);
  return (
    <div>
      <button onClick={() => setOn(!on)}>toggle</button>
      <div contentEditable suppressContentEditableWarning>
        {on ? <b>bold</b> : null}
        <i>italic</i>
      </div>
    </div>
  );
}
