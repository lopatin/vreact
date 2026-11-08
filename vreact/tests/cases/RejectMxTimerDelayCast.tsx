// expect: reject type assertions are not allowed in VTS (they are unchecked casts); the delay of setTimeout/setInterval
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// the delay of a timer is evaluated by JS but not translated: a cast in it could clear the state Map
export function C() {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map([[1, 1]]));
  invariant(s.size === 1);
  useEffect(() => {
    const id = setTimeout(() => setS(new Map(s)), (s as any).clear() ?? 10);
    return () => clearTimeout(id);
  }, [s]);
  return <p>{s.size}</p>;
}
