// expect: reject id="nodeName" on <p>: HTML's named access makes this element the global nodeName
// window.nodeName is this <p> (the window defines no nodeName); react-dom 18.3.1 uses the window
// as the target node of an event that has no target fiber (ChangeEventPlugin, SelectEventPlugin:
// a selectionchange, a mouseout of the root container), and window.nodeName.toLowerCase() throws
// there, so the event's handlers (onMouseEnter) never run.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Hover() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <p id="nodeName">{n}</p>
      <button type="button" onMouseEnter={() => setN((m) => m + 1)}>hover</button>
    </div>
  );
}
