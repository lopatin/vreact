// expect: reject <Tree> inside Tree: a component that refers to itself
// The self-reference in an early return of the render.
import { type int } from "vreact/spec";
export function Tree(props: { readonly d: int }) {
  if (props.d > 0) {
    return <section><Tree d={props.d - 1} /></section>;
  }
  return <p>leaf</p>;
}
