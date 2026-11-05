// expect: reject capture-phase handlers (onClickCapture)
// Handler classification is a whitelist of React 18's own event props: a capture
// handler (same native click as the button's onClick) is not silently "discrete".
import { useState } from "react";
export function Bad() {
  const [n, setN] = useState(0);
  return (
    <div onClickCapture={() => setN(n + 1)}>
      <button onClick={() => setN(n + 1)}>{n}</button>
    </div>
  );
}
