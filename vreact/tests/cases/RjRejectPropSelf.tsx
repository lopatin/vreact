// expect: reject a prop named __self
// The same for __self (a callback prop too: the child would call undefined).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
function Clicker(props: { readonly __self: () => void }) {
  return <button type="button" onClick={() => props.__self()}>+</button>;
}
export function RjPropSelf() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <Clicker __self={() => setN(n + 1)} />;
}
