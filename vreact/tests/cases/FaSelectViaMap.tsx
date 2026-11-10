// expect: reject <input> inside <option>: an <option> may contain only text
// ... and inside the options of a keyed list: one click on a checkbox in an option runs the
// <div>'s onClick and the select's onChange in one batch.
import { useState } from "react";
import { type int, distinct, invariant, requires } from "vreact/spec";

export function FaSelectViaMap(props: { opts: readonly string[] }) {
  requires(distinct(props.opts));
  const [a, setA] = useState<int>(0);
  const [b, setB] = useState<int>(0);
  invariant(a >= 0 && b >= 0 && a + b <= 1);
  return (
    <div onClick={() => { if (a + b < 1) setB(b + 1); }}>
      <select value="x" onChange={() => { if (a + b < 1) setA(a + 1); }}>
        {props.opts.map((o) => <option key={o} value={o}>{o}<input type="checkbox" /></option>)}
      </select>
    </div>
  );
}
