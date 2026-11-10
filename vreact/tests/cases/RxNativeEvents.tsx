// expect: verified
// Handlers that no single native event reaches together are accepted: a text
// input's onChange (native input/change) inside an onClick row (native click),
// and a checkbox's onChange next to (not inside) a clickable label.  Robust
// (continuous) handlers may share a native event: onMouseEnter/onMouseLeave.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Row() {
  const [text, setText] = useState<string>("");
  const [clicks, setClicks] = useState<int>(0);
  const [on, setOn] = useState(false);
  const [hover, setHover] = useState(false);
  const [moves, setMoves] = useState<int>(0);
  const [wheel, setWheel] = useState<int>(0);
  invariant(clicks >= 0 && text.length <= 20 && moves >= 0);
  return (
    <div>
      <p onMouseEnter={() => setHover(true)} onMouseLeave={() => setHover(false)}
        onMouseMove={() => setMoves((m) => m + 1)} onWheel={() => setWheel((w) => w + 1)}>{hover ? "in" : "out"} {moves} {wheel}</p>
      <div onClick={() => setClicks(clicks + 1)}>
        <input type="text" value={text} onChange={(e) => { if (e.target.value.length <= 20) setText(e.target.value); }} />
      </div>
      <span onClick={() => setClicks(0)}>reset</span>
      <input type="checkbox" checked={on} onChange={() => setOn(!on)} />
    </div>
  );
}
