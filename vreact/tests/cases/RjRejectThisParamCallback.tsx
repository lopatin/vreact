// expect: reject a `this` parameter is not supported
// A callback prop written with a `this` parameter: JS gives `b` the first argument (5), the
// positional binding gave it the second one.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

const XS: readonly string[] = ["x", "y"];

type CProps = { readonly onPick: (a: int, b: int) => void };
export function RjThisChild(props: CProps) {
  return <button onClick={() => props.onPick(5, 0)}>pick</button>;
}

export function RjThisParent() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 1);
  return (
    <div>
      <RjThisChild onPick={function (this: int, b: int) { if (b === 0) setN(b); }} />
      <p>{XS[n].length}</p>
    </div>
  );
}
