// expect: reject `onA` is not a name destructured from the props parameter of C
// The identifier `onA` here is the module's function onA, not the callback prop props.onA: the
// contract used to be attached to props.onA by the identifier's spelling.
import { callbackRequires, type int } from "vreact/spec";

function onA(i: int): int {
  return i;
}

type CP = { readonly onA: (i: int) => void };
export function C(props: CP) {
  callbackRequires(onA, (i) => i > 0);
  return <button onClick={() => props.onA(-1)}>c</button>;
}
