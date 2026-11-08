// expect: reject a prop named ref
// React 18 does not pass `ref` to a function component (props.ref is undefined).
import { type int } from "vreact/spec";
function Item(props: { readonly ref: int }) {
  return <p>{props.ref}</p>;
}
export function RjPropRef() {
  return <Item ref={2} />;
}
