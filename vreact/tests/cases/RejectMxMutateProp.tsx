// expect: reject is not a local variable of this function
import { type int } from "vreact/spec";

export function Show(props: { readonly m: Map<int, int> }) {
  return <button onClick={() => { props.m.delete(1); }}>{props.m.size}</button>;
}
