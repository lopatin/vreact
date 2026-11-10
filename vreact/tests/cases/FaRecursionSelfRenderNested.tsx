// expect: reject <Tree> inside Tree: a component that refers to itself
// The self-reference inside an element, under a condition on state (round-2 finding state-r2-4).
import { useState } from "react";
import { type int } from "vreact/spec";
export function Tree(props: { readonly depth: int }) {
  const [open, setOpen] = useState<boolean>(false);
  return (
    <div>
      <button onClick={() => setOpen(!open)}>t</button>
      {open && props.depth > 0 ? <Tree depth={props.depth - 1} /> : null}
    </div>
  );
}
