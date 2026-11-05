// expect: reject before any early return (Rules of Hooks)
// A switch with an early return makes the hooks after it conditional.
import { useState } from "react";
import { type int } from "vreact/spec";
type Mode = "a" | "b";
export function CtlAfterSwitch(props: { readonly mode: Mode }) {
  switch (props.mode) {
    case "a":
      return <p>a</p>;
    default:
      break;
  }
  const [n, setN] = useState<int>(0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
