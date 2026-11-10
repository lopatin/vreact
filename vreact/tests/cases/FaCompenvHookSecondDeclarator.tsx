// expect: reject declare a useState on its own
// A useState that is not the first declarator of its declaration (formerly a crash: "Cannot read
// properties of undefined (reading 'name')").
import { useState } from "react";
import { type int } from "vreact/spec";

export function C() {
  const x: int = 1, [n, setN] = useState<int>(0);
  return <button onClick={() => setN(n + x)}>{n}</button>;
}
