// expect: verified
// The parent relies on the child's callback contract to keep its own invariant.
import { useState } from "react";
import { requires, invariant, callbackRequires, type int } from "vreact/spec";
type ChooserProps = { readonly n: int; readonly onChoose: (i: int) => void };
export function Chooser(props: ChooserProps) {
  requires(props.n > 0);
  callbackRequires(props.onChoose, (i) => 0 <= i && i < props.n);
  return (
    <div>
      <button onClick={() => props.onChoose(0)}>first</button>
      <button onClick={() => props.onChoose(props.n - 1)}>last</button>
    </div>
  );
}
export function Host() {
  const [labels] = useState<readonly string[]>(["x", "y", "z"]);
  const [idx, setIdx] = useState<int>(0);
  invariant(labels.length === 3 && 0 <= idx && idx < labels.length);
  return (
    <div>
      <p>{labels[idx]}</p>
      <Chooser n={labels.length} onChoose={(i) => setIdx(i)} />
    </div>
  );
}
