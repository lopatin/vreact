// expect: reject type assertions are not allowed in VTS
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// an effect cleanup (not translated) clears the state Map through a cast
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map([[1, 1]]));
  invariant(s.size === 1);
  useEffect(() => {
    return () => {
      console.log((s as any).clear());
    };
  }, [s]);
  return <button onClick={() => setS(new Map(s))}>{s.size}</button>;
}
