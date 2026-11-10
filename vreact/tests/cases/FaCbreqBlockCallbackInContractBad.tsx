// expect: fail callback-contract
// A block-bodied some inside an expression-bodied callbackRequires lambda (read as code) still
// constrains the calls: onPick(5) must show that 5 is one of props.ids, which nothing establishes.
import { callbackRequires, type int } from "vreact/spec";

type CP = { readonly ids: readonly int[]; readonly onPick: (id: int) => void };
export function Child(props: CP) {
  callbackRequires(props.onPick, (id) => props.ids.some((x) => { return x === id; }));
  return <button onClick={() => props.onPick(5)}>a</button>;
}
