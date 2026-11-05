// expect: reject a default value for parameter `v` is not supported
// JS replaces an undefined argument by the default (v is 5 here, so x becomes 2).
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";
type P = { readonly onPick: (v: int | undefined) => void };
export function Child(props: P) {
  callbackRequires(props.onPick, (v) => v === undefined);
  return <button onClick={() => props.onPick(undefined)}>x</button>;
}
export function App() {
  const [x, setX] = useState<int>(0);
  invariant(x <= 1);
  return <Child onPick={(v: int | undefined = 5) => setX(v === undefined ? 1 : 2)} />;
}
