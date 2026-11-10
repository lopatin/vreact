// expect: reject mutually recursive declarations are not supported
// A longer render cycle (A → B → C → A), through a map callback in B and a JSX constant in C:
// every reference between components counts, wherever it is in the body.
import { type int } from "vreact/spec";
export function A(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <B ds={[props.d - 1]} /> : null}</div>;
}
export function B(props: { readonly ds: readonly int[] }) {
  return <ul>{props.ds.map((x) => <li key={x}>{x > 0 ? <C d={x - 1} /> : null}</li>)}</ul>;
}
export function C(props: { readonly d: int }) {
  const child = <A d={props.d - 1} />;
  return <div>{props.d > 0 ? child : null}</div>;
}
