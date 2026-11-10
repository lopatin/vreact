// expect: fail callback-contract
// The conjunct about the parameter the first contract ignores is checked at the call:
// onPair(1, -2) breaks `y > 0`.
import { type int, callbackRequires } from "vreact/spec";

type P = { onPair: (a: int, b: int) => void };

export function Child(props: P) {
  callbackRequires(props.onPair, (a) => a > 0);
  callbackRequires(props.onPair, (x, y) => y > 0);
  return <button onClick={() => props.onPair(1, -2)}>a</button>;
}
