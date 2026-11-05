// expect: reject parameter `v` is annotated `unknown` but receives a value of type `int | undefined`
// callbackRequires: the contract's parameters are the callback prop's arguments.
import { callbackRequires, type int } from "vreact/spec";
type P = { readonly onPick: (v: int | undefined) => void };
export function Picker(props: P) {
  callbackRequires(props.onPick, (v: unknown) => v === null);
  return <button onClick={() => props.onPick(undefined)}>x</button>;
}
