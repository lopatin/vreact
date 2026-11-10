// expect: reject inside <svg>: React would create its elements in the SVG namespace
// A component rendered inside <svg> is verified as an HTML tree, but React creates its
// elements in the SVG namespace (its <input> would have no value).
import { useState } from "react";

export function RjSvgChild() {
  const [s, setS] = useState<string>("");
  return <input value={s} onChange={(e) => setS(e.currentTarget.value)} />;
}

export function RjSvgComponent() {
  return (
    <svg width="10" height="10">
      <RjSvgChild />
    </svg>
  );
}
