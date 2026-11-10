// expect: reject effect cleanups may only clear timers
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// an effect-local helper named `clearTimeout` is not the global: the cleanup (not translated)
// would set the state when the dependency changes
export function C(props: { readonly k: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n === 0);
  useEffect(() => {
    const clearTimeout = (id: int) => setN(id);
    return () => clearTimeout(1);
  }, [props.k]);
  return <p>{n}</p>;
}
