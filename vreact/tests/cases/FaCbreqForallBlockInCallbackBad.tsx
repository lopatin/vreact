// expect: fail callback-contract
// A block-bodied forall inside a callbackRequires lambda (read as code) still constrains the
// calls: onPick(0) breaks it for k = 0.
import { callbackRequires, forall, requires, type int } from "vreact/spec";

type CP = { readonly n: int; readonly onPick: (i: int) => void };
export function C(props: CP) {
  requires(props.n > 0);
  callbackRequires(props.onPick, (i) => forall(0, props.n, (k) => { return k !== i; }));
  return <button onClick={() => props.onPick(0)}>c</button>;
}
