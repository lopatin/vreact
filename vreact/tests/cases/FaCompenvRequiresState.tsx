// expect: reject a requires(…) may mention only the props and top-level declarations
// A component's requires(…) is about the props (what the parent establishes): one that reads
// state is rejected with that reason (formerly "unknown or unsupported identifier").
import { useState } from "react";
import { invariant, requires, type int } from "vreact/spec";
export function C(props: { readonly x: int }) {
  const [a, setA] = useState<int>(0);
  requires(props.x > a);
  invariant(a >= 0);
  return <button onClick={() => setA(0)}>{a}</button>;
}
