// expect: verified
// Default-priority handlers (onTransitionEnd, onLoad, …) are checked like
// continuous ones: robust (guard inside the functional update). The click is then
// checked against the states rebasing may produce (here: robust as well).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Fade() {
  const [finished, setFinished] = useState<int>(0);
  invariant(0 <= finished && finished <= 1);
  return (
    <div className="fade" onTransitionEnd={() => setFinished((f) => (f < 1 ? f + 1 : f))} onLoad={() => setFinished((f) => f)}>
      <button onClick={() => setFinished(0)}>{finished}</button>
    </div>
  );
}
