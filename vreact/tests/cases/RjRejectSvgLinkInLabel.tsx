// expect: reject onClick on <a> inside a <label>
// An HTML <a href> is interactive content, which stops a label's activation; an SVG <a href>
// (inside <svg>) is not HTML interactive content: a click on it runs its onClick and the label
// clicks its control again, in one batch when a script dispatches the click.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjSvgLinkInLabel() {
  const [n, setN] = useState<int>(0);
  const [on, setOn] = useState(false);
  return (
    <label>
      <input type="checkbox" checked={on} onChange={() => setOn(!on)} />
      <svg width="10" height="10">
        <a href="#x" onClick={() => setN(n + 1)}>
          <rect width="5" height="5" />
        </a>
      </svg>
    </label>
  );
}
