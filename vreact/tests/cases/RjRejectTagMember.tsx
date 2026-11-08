// expect: reject is a dynamic element type
// `<props.as>` renders whatever props.as holds (here a <button>), not an element named
// "props.as": a member-expression tag is a dynamic element type, which is not modelled.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function RjTag(props: { readonly as: "button" }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <props.as onClick={() => setN(n + 1)}>{n}</props.as>;
}
