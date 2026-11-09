// expect: reject a timer's delay may not call `m.get(1)!.push` here
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// the array stored in the state Map is mutated by the timer's delay
export function MapArr() {
  const [m, setM] = useState<ReadonlyMap<int, int[]>>(new Map([[1, []]]));
  const [k, setK] = useState(0);
  invariant([...m.values()].every((a) => a.length === 0) && k >= 0);
  useEffect(() => {
    const id = setTimeout(() => setM(new Map(m)), m.get(1)!.push(5) * 1000000);
    return () => clearTimeout(id);
  }, [m]);
  return <button onClick={() => setK(k + 1)}>{m.get(1)?.length ?? 0}</button>;
}
