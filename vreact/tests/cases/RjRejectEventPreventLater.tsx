// expect: reject is read inside a functional update
// e.preventDefault() inside a functional update runs after the dispatch (too late to
// prevent anything): the event may only be used in the handler's own statements.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjEventPreventLater() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <form onSubmit={(e) => setN((p) => { e.preventDefault(); return p + 1; })}><p>{n}</p></form>;
}
