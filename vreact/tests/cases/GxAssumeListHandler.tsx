// expect: status Board=assumes
// assume(…) stays available where Lean's context is the program's: in a handler of a keyed list
// item (the item comes with its membership `it ∈ items`, the state with the invariant), in an
// effect, a timer callback or a callback passed to a child (Cx… cases). Rejected only where Lean
// checks a body for more values than JS gives it (GxRejectAssume… cases).
import { useState } from "react";
import { assume, distinct, invariant, type int } from "vreact/spec";

type Item = { readonly id: int; readonly qty: int };

export function Board() {
  const [items] = useState<readonly Item[]>([]);
  const [total, setTotal] = useState<int>(0);
  invariant(total >= 0 && distinct(items, (i) => i.id));
  return (
    <ul>
      {items.map((it) => (
        <li key={it.id}>
          <button
            onClick={() => {
              assume(it.qty >= 0);
              setTotal(total + it.qty);
            }}
          >
            {it.qty}
          </button>
        </li>
      ))}
    </ul>
  );
}
