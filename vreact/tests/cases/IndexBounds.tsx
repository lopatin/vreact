// expect: fail index
import { useState } from "react";
import { type int } from "vreact/spec";
export function IndexBounds() {
  const [xs] = useState<readonly string[]>(["a"]);
  const [i, setI] = useState<int>(0);
  return <button onClick={() => setI(i + 1)}>{xs[i]}</button>;
}
