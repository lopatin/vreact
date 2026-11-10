// expect: reject parameter `p` is annotated `unknown` but receives a value of type `int | undefined`
// A functional update's parameter is the current state (int | undefined here), whatever it is
// annotated.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function App() {
  const [x, setX] = useState<int | undefined>(undefined);
  invariant(x === undefined);
  return <button onClick={() => setX((p: unknown) => (p === null ? undefined : 2))}>x</button>;
}
