// expect: reject mutually recursive declarations are not supported
// Two components that render each other (a recursion that terminates in React: d decreases)
// are recursion: the cycle check of the component order rejects them before Lean runs (a
// component's Lean render would otherwise mention the other's component before it is defined).
import { type int } from "vreact/spec";
export function A(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <B d={props.d - 1} /> : null}</div>;
}
export function B(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <A d={props.d - 1} /> : null}</div>;
}
