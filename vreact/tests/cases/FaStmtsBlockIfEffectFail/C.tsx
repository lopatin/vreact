// expect: fail effect-robust C=incomplete unchecked=0 errors=none
// The effect after a branching block is still checked on every path: on the path where x is
// present it may set a negative n (formerly the render did not elaborate and nothing was checked).
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";
export function C(props: { readonly x: int | null }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const x = props.x;
  {
    if (x !== null) {
      console.log("present");
    }
  }
  useEffect(() => {
    if (x !== null) setN(x);
  }, [x]);
  return <p>{n}</p>;
}
