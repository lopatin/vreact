// expect: reject <T> inside T: a component that refers to itself
// A component that renders itself (a recursive tree; it terminates for d >= 0 in React) was
// not rejected: Lean met `T.component.node` inside `T.render`, before it is defined, and the
// report showed an internal error as a failed child-precondition (round-2 findings combo-r2-2,
// jsx-r2-1, lean-r2-1). Recursion is not supported: rejected before Lean runs.
import { requires, type int } from "vreact/spec";
export function T(props: { readonly d: int }) {
  requires(props.d >= 0);
  return props.d > 0 ? <T d={props.d - 1} /> : <p>end</p>;
}
