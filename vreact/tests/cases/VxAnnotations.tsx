// expect: verified
// Parameter annotations that are exactly the type of the value received are accepted: ensures
// (the return type, also an inline record), callbackRequires (the callback's parameters),
// handlers and functional updates, array-method callbacks, quantifiers.
import { useState } from "react";
import { callbackRequires, ensures, forall, implies, invariant, type int } from "vreact/spec";
type R = { readonly v?: int };
type P = { readonly onPick: (r: R, k: int | null) => void };
export function Child(props: P) {
  callbackRequires(props.onPick, (r: R, k: int | null) => r.v === undefined && k === null);
  return <button onClick={() => props.onPick({}, null)}>x</button>;
}
export function App() {
  const [x, setX] = useState<int | undefined>(undefined);
  invariant(x === undefined || x === 1);
  return <Child onPick={(r: R, k: int | null) => setX((p: int | undefined) => (r.v === undefined && k === null && p === undefined ? 1 : p))} />;
}
export function g(xs: readonly (int | undefined)[]): int {
  ensures((r: int) => implies(xs.every((x: int | undefined) => x !== undefined), r === 0));
  return xs.filter((x: int | undefined) => x === undefined).length;
}
export function h(xs: readonly { readonly v?: int }[]): readonly { readonly v?: int }[] {
  ensures((r: readonly { readonly v?: int }[]) => forall(0, xs.length, (i: int) => xs[i].v === xs[i].v));
  return xs.filter((x: { readonly v?: int }) => x.v === undefined);
}
export function mk(x: int): { readonly v: int } {
  ensures((r: { readonly v: int }) => r.v === x);
  return { v: x };
}
