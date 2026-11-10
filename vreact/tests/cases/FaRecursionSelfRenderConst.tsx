// expect: reject <Tree> inside Tree: a component that refers to itself
// The self-reference in a JSX constant, rendered only under a condition.
import { type int } from "vreact/spec";
export function Tree(props: { readonly d: int }) {
  const child = <Tree d={props.d - 1} />;
  return <div>{props.d > 0 ? child : null}</div>;
}
