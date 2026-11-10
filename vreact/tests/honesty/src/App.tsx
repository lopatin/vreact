import { useState } from "react";
import { invariant, requires, type int } from "vreact/spec";
import { clamp, inc, LIMIT } from "./model";
type ShowProps = { readonly value: int };
export function Show(props: ShowProps) {
  requires(props.value >= 0);
  return <span>{props.value}</span>;
}
export function App() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= LIMIT);
  return (
    <div>
      <Show value={n} />
      <button onClick={() => setN(clamp(inc(n)))}>+1</button>
    </div>
  );
}
