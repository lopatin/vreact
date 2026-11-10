// expect: reject mutually recursive declarations are not supported
// A verified component that renders a @trusted one whose body renders it back is a render cycle
// too: the cycle check also reads the bodies of @trusted components (only a @trusted
// component's reference to itself is allowed: FaRecursionTrustedSelf).
import { type int } from "vreact/spec";
export function A(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <W d={props.d - 1} /> : null}</div>;
}
/** @trusted */
export function W(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <A d={props.d - 1} /> : null}</div>;
}
