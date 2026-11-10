// expect: reject declare the result of useMemo(…) with const, not let
import { useState, useMemo } from "react";
import { int } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  let d = useMemo(() => n + 1, [n]);
  return <button onClick={() => setN(n + 1)}>{d}</button>;
}
