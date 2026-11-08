import { type int } from "vreact/spec";

export function Label(props: { readonly n: int }) {
  return <p>{props.n}</p>;
}
