// expect: verified
// Both contracts are guaranteed by the child and assumed by the parent, whose
// invariant needs both.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";
type PickerProps = { readonly onPick: (i: int) => void };
export function Picker(props: PickerProps) {
  callbackRequires(props.onPick, (i) => i >= 0);
  callbackRequires(props.onPick, (j) => j < 10);
  return <button onClick={() => props.onPick(3)}>pick</button>;
}
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n < 10);
  return <div><Picker onPick={(i) => setN(i)} />{n}</div>;
}
