// expect: reject <Node> inside Node: a component that refers to itself
// The self-reference in a map callback (a nested list).
import { type int } from "vreact/spec";
export function Node(props: { readonly ids: readonly int[] }) {
  return <ul>{props.ids.map((id) => <li key={id}><Node ids={[]} /></li>)}</ul>;
}
