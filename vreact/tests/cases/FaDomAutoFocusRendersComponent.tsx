// expect: reject onFocus on <input> with autoFocus updates state, and a later render of Host may mount an autoFocus element (Host renders <Field>
// A component that renders another component may mount autoFocus elements when it re-renders
// (the child's, under a condition of its props), so the focus handlers of its own autoFocus
// elements, and of the elements around them, may not update state: the bound on the chain of
// nested commits (FaDomAutoFocusTrack) needs these updates to mount no autoFocus element.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

export function Field(props: { readonly n: int }) {
  return props.n % 2 === 0 ? <textarea autoFocus /> : <p>{props.n}</p>;
}

export function Host() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <input autoFocus onFocus={() => setN((m) => m + 1)} />
      <Field n={n} />
    </div>
  );
}
