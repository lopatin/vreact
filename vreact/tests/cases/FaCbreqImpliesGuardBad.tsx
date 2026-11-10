// expect: fail callback-contract
// The guarded implies contract still constrains the calls: onPick(0) must show xs[0] >= 0 when
// xs is non-empty, which nothing establishes.
import { callbackRequires, implies, type int } from "vreact/spec";

type CP = { readonly xs: readonly int[]; readonly onPick: (i: int) => void };
export function C(props: CP) {
  callbackRequires(props.onPick, (i) => implies(0 <= i && i < props.xs.length, props.xs[i] >= 0));
  return <button onClick={() => props.onPick(0)}>c</button>;
}
