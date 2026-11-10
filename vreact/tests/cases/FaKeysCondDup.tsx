// expect: fail unique-keys App=incomplete Item=verified
// A conditional child is in the same array as its siblings: while it is shown, two children
// have the key "a" (lean-r1-1: React then never removes the first Item when it is hidden).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function Item(props: { readonly label: string }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n);
  return <button onClick={() => setN(n + 1)}>{props.label} {n}</button>;
}
export function App() {
  const [show, setShow] = useState<boolean>(true);
  return (
    <div>
      <input type="checkbox" checked={show} onChange={(e) => setShow(e.target.checked)} />
      {show && <Item key="a" label="first" />}
      <Item key="a" label="second" />
    </div>
  );
}
