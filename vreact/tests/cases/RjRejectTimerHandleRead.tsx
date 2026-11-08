// expect: reject is a timer handle: it can only be cleared
// A timer handle is not a VTS value (a browser-chosen positive integer): it can only be
// passed to clearTimeout / clearInterval in the effect's cleanup.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function RjTimerHandleRead() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const id = setTimeout(() => setN((k) => k + 1), 1000);
    return () => console.log("timer", id);
  }, []);
  return <p>{n}</p>;
}
