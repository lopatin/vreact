// expect: fail callback-contract
// Two callbackRequires for one callback are conjoined: onPick(-5) violates the
// first one (it used to be silently replaced by the second).
import { callbackRequires, type int } from "vreact/spec";
type PickerProps = { readonly onPick: (i: int) => void };
export function Picker(props: PickerProps) {
  callbackRequires(props.onPick, (i) => i >= 0);
  callbackRequires(props.onPick, (j) => j < 10);
  return <button onClick={() => props.onPick(-5)}>pick</button>;
}
