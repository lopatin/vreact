// expect: reject assigning it from inside a function or callback is not supported
// A handler assigning a render-local `let`: the write is shared with every closure of the render.
import { useState } from "react";
import { type int } from "vreact/spec";
export function CtlHandlerWrite() {
  const [n, setN] = useState<int>(0);
  let next: int = n + 1;
  return <button onClick={() => { next = 0; setN(next); }}>{n}</button>;
}
