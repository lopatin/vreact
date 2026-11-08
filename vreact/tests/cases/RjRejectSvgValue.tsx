// expect: reject <input> inside <svg> is an SVG element named input, not an HTML one
// React creates the elements inside <svg> in the SVG namespace: this <input> has no value, so
// e.currentTarget.value is undefined and s.length throws after a click.
import { useState } from "react";
import { invariant } from "vreact/spec";

export function RjSvgValue() {
  const [s, setS] = useState<string>("abc");
  invariant(s.length >= 0);
  return (
    <div>
      <svg width="10" height="10">
        <input onClick={(e) => setS(e.currentTarget.value)} />
      </svg>
      <p>{s.length}</p>
    </div>
  );
}
