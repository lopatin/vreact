// expect: verified
// A render-local const whose index obligation uses the invariant / precondition must not
// hide hinv / hpre from the later obligations (handlers, keys).
import { useState } from "react";
import { invariant, requires, distinct, type int } from "vreact/spec";

export function LnCur() {
  const [xs] = useState<readonly string[]>(["a", "b", "c"]);
  const [i, setI] = useState<int>(0);
  invariant(xs.length === 3 && 0 <= i && i < xs.length);
  const cur = xs[i];
  return <button onClick={() => setI(i + 1 < xs.length ? i + 1 : 0)}>{cur}</button>;
}

type P = { readonly items: readonly string[] };
export function LnFirst(props: P) {
  requires(props.items.length > 0 && distinct(props.items));
  const first = props.items[0];
  return (
    <div>
      <b>{first}</b>
      <ul>{props.items.map((s) => <li key={s}>{s}</li>)}</ul>
    </div>
  );
}
