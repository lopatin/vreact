// expect: reject prop cbs has the function type () => void, which is not data
// Only a direct field of the props may be a callback (an array of them: formerly an internal
// error).
import { type int } from "vreact/spec";

export function RnFnInProps(props: { readonly cbs: readonly (() => void)[]; readonly n: int }) {
  return <p>{props.cbs.length + props.n}</p>;
}
