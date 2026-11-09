// expect: reject is not a valid React child
import { type int } from "vreact/spec";

export function App(props: { readonly m: ReadonlyMap<int, string> }) {
  return <p>{props.m}</p>;
}
