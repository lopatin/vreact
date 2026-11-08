// expect: reject unreachable code after return
// Code after the component's return never runs either.
import { type int } from "vreact/spec";
export function RjRenderAfterReturn(props: { readonly xs: readonly int[] }) {
  return <p>{props.xs.length}</p>;
  const x = props.xs[0];
}
