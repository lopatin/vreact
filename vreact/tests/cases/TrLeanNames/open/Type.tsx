import { requires, type int } from "vreact/spec";
import { Sort } from "../end/Sort";

export function Option(props: { readonly k: int }) {
  requires(props.k > 0);
  return <section><Sort /></section>;
}
