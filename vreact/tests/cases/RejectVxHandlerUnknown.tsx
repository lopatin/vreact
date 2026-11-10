// expect: reject parameter `v` is annotated `unknown` but receives a value of type `int | undefined`
// For a callback, TypeScript only checks that the annotation accepts the argument: `unknown` hides
// that v is undefined (never null), and `v === null` would be read as "absent". In JS the click
// sets x to 2, breaking the invariant.
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
  return <Child onPick={(v: unknown) => setX(v === null ? 1 : 2)} />;
}
