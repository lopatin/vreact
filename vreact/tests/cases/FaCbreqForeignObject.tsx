// expect: reject `Math` is not the props parameter of C
// `Math.max` is not a callback prop, although the component has a callback prop named max: the
// contract used to be attached to props.max by the property's spelling.
import { callbackRequires, type int } from "vreact/spec";

type CP = { readonly max: (a: int, b: int) => void };
export function C(props: CP) {
  callbackRequires(Math.max, (a, b) => a < b);
  return <button onClick={() => props.max(2, 1)}>c</button>;
}
