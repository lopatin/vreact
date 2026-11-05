// expect: fail handler
// switch (props.mode) is translated as a match on the enum: the unguarded "inc" arm
// breaks the invariant, and is reported.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
type Mode = "inc" | "reset";
export function App(props: { readonly mode: Mode }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  return (
    <button onClick={() => {
      switch (props.mode) {
        case "inc":
          setN(n + 1);
          break;
        default:
          setN(0);
          break;
      }
    }}>{n}</button>
  );
}
