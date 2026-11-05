// expect: reject one native "click" event would run both (event bubbling)
// With a non-literal `type`, the input may be a checkbox: its onChange may come
// from the same native click as the enclosing onClick.
import { useState } from "react";
type Props = { readonly kind: string };
export function Bad(props: Props) {
  const [n, setN] = useState(0);
  return (
    <div onClick={() => setN(1)}>
      <input type={props.kind} onChange={() => setN(2)} />
      {n}
    </div>
  );
}
