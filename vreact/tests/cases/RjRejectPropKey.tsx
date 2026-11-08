// expect: reject a prop named key
// React takes `key` out of the props: <Item key={1} /> gives the component props.key ===
// undefined, so a prop named key cannot be modelled as the value the parent passes.
import { type int } from "vreact/spec";
function Item(props: { readonly key: int; readonly label: string }) {
  return <p>{props.key + 1} {props.label}</p>;
}
export function RjPropKey() {
  return <Item key={1} label="a" />;
}
