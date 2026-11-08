// expect: verified errors=none
import { useState } from "react";
import { distinct, invariant, requires, type int } from "vreact/spec";

// a Set in state: toggling a selection in a functional update (bounded)
export function Picker(props: { readonly ids: readonly int[] }) {
  requires(distinct(props.ids));
  const [sel, setSel] = useState(new Set<int>());
  invariant(sel.size <= 3);
  return (
    <ul>
      {props.ids.map((id) => (
        <li key={id}>
          <input
            type="checkbox"
            checked={sel.has(id)}
            onChange={() =>
              setSel((s) => {
                const n = new Set(s);
                if (n.has(id)) n.delete(id);
                else if (n.size < 3) n.add(id);
                return n;
              })
            }
          />
        </li>
      ))}
      <li>{sel.size} selected</li>
    </ul>
  );
}
