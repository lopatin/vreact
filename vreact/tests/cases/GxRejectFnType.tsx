// expect: reject generic function types are not supported in VTS
// A generic callback type.
import { type int } from "vreact/spec";
type P = { readonly n: int; readonly onPick: <T>(x: T) => void };
export function Pick(props: P) {
  return <button onClick={() => props.onPick(props.n)}>{props.n}</button>;
}
