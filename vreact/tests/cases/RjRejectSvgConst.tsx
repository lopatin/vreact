// expect: reject <input> inside <svg> is an SVG element named input
// A JSX const is created where it is declared but its elements get the namespace of the place
// where it is rendered: this <input>, rendered inside <svg>, is an SVG element (no value).
import { useState } from "react";

export function RjSvgConst() {
  const [s, setS] = useState<string>("");
  const field = <input value={s} onChange={(e) => setS(e.currentTarget.value)} />;
  return (
    <div>
      <svg width="10" height="10">
        <g>{field}</g>
      </svg>
      <p>{s.length}</p>
    </div>
  );
}
