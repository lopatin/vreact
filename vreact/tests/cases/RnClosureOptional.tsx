// expect: reject optional parameter `step?` of the local function bump is not supported
// An optional parameter of a useCallback helper (it receives `int | undefined`, while the
// translation typed it `int`).
import { useCallback, useState } from "react";
import { type int } from "vreact/spec";

export function RnClosureOptional() {
  const [n, setN] = useState<int>(0);
  const bump = useCallback((step?: int) => setN(n + 1), [n]);
  return <button type="button" onClick={() => bump(1)}>{n}</button>;
}
