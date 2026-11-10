// expect: reject the useEffect function reads `step`, declared after the useEffect call
// An effect that reads a const declared after the useEffect call cannot list it in its
// dependency array (temporal dead zone): React would keep running the effect of an earlier
// render. Rejected with that reason (formerly "unknown or unsupported identifier").
import { useState, useEffect } from "react";
import { type int, invariant } from "vreact/spec";

export function C(props: { readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    setN((k) => k + step);
  }, []);
  const step: int = props.fast ? 2 : 1;
  return <p>{n}</p>;
}
