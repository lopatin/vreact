// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { type int } from "vreact/spec";

function Child(props: { readonly m: ReadonlyMap<int, int> }) {
  return <p>{props.m.size}</p>;
}
// the element is created with the Map, which is mutated before it is rendered
export function App() {
  const n = new Map<int, int>();
  const row = <Child m={n} />;
  n.set(1, 1);
  return <div>{row}</div>;
}
