// expect: reject `Tree` inside Tree: a component that refers to itself
// A component that refers to itself as a value (an alias of itself used as a tag).
import { type int } from "vreact/spec";
export function Tree(props: { readonly d: int }) {
  const C = Tree;
  return <div>{props.d > 0 ? <C d={props.d - 1} /> : null}</div>;
}
