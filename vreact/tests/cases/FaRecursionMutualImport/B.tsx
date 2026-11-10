import { type int } from "vreact/spec";
import { A } from "./A";
export function B(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <A d={props.d - 1} /> : null}</div>;
}
