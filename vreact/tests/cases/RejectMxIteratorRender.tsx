// expect: reject is an iterator, which JS consumes once
import { type int } from "vreact/spec";

// React DEV iterates an iterable child twice (key check, then render): a one-shot iterator renders nothing
export function App(props: { readonly m: ReadonlyMap<int, string> }) {
  return <p>{props.m.values()}</p>;
}
