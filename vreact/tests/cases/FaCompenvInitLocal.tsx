// expect: reject an initial value (useState / useReducer) may read only the props, the state values declared before it
// A render-local const read by an initial value: rejected with the restriction (formerly
// "unknown or unsupported identifier `k` (only locals, …)", false: `k` is a local).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function C(props: { readonly x: int }) {
  const k: int = props.x * 2;
  const [a, setA] = useState<int>(k);
  invariant(a === a);
  return <button onClick={() => setA(0)}>{a}</button>;
}
