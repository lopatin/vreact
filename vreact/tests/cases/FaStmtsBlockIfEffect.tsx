// expect: verified
// A block before a hook may branch without returning (`{ if (x !== null) { … } }`, a switch in a
// block): the hooks after it still run unconditionally, once per render. Each path's render carries
// each effect once, translated where that path reaches it (formerly the else path also carried the
// copy translated under the then-branch's narrowing: "Unknown identifier `x_1`").
import { useEffect, useMemo, useState } from "react";
import { invariant, type int } from "vreact/spec";
type P = { readonly x: int | null; readonly k: int };
export function C(props: P) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const x = props.x;
  useEffect(() => {
    console.log("mounted");
  }, []);
  {
    if (x !== null) {
      console.log("present");
    }
  }
  useEffect(() => {
    console.log(x);
  }, [x]);
  {
    switch (props.k) {
      case 1:
        console.log("one");
        break;
      default:
        break;
    }
  }
  const shown = useMemo(() => (x === null ? 0 : x), [x]);
  useEffect(() => {
    setN(x === null || x < 0 ? 0 : x);
  }, [x]);
  return <button onClick={() => setN(n + 1)}>{n + shown}</button>;
}
