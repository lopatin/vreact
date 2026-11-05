// expect: fail callback-contract
// The child promises to call onPick only with an index in range, but doesn't check.
import { callbackRequires, type int } from "vreact/spec";
type PickerProps = { readonly n: int; readonly onPick: (i: int) => void };
export function Picker(props: PickerProps) {
  callbackRequires(props.onPick, (i) => 0 <= i && i < props.n);
  return <button onClick={() => props.onPick(props.n)}>pick last</button>;
}
