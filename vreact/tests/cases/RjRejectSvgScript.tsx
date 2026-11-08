// expect: reject <script> is not supported: its code is outside the verified program
// Sibling of RjRejectSvgValue: inside <svg>, React creates the <script> with createElementNS, and
// an SVG script runs when React inserts it (an HTML one, which React creates through innerHTML,
// does not): code outside the program that may change the DOM React manages.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjSvgScript() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      {n > 0 ? (
        <svg width="10" height="10">
          <script>{"document.body.textContent = '';"}</script>
        </svg>
      ) : null}
    </div>
  );
}
