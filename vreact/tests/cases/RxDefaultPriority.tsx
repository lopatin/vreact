// expect: fail handler-robust
// transitionend has React's DefaultEventPriority: not flushed synchronously. Two
// transitions ending in one frame run the same closure (finished = 0) twice.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Fade() {
  const [finished, setFinished] = useState<int>(0);
  invariant(0 <= finished && finished <= 1);
  return (
    <div className="fade" onTransitionEnd={() => { if (finished < 1) setFinished((f) => f + 1); }}>
      {finished}
    </div>
  );
}
