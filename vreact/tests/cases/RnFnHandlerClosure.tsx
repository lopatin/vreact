// expect: reject parameter `gs` of bump has the function type () => void, which is not data
// A local closure called as a statement of a handler binds its parameters to its arguments as
// data: an array of functions has none (formerly an internal error).
import { useState } from "react";
import { type int } from "vreact/spec";

export function App() {
  const [n, setN] = useState<int>(0);
  const bump = (gs: readonly (() => void)[]) => setN(n + gs.length);
  return <button onClick={() => bump([])}>{n}</button>;
}
