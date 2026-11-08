// expect: reject a prop named key
// A props type that spells the name as a string ("key") declares the same prop.
import { type int } from "vreact/spec";
interface P {
  readonly "key": int;
}
function Item(props: P) {
  return <p>{props.key + 1}</p>;
}
export function RjPropKeyQuoted() {
  return <Item key={1} />;
}
