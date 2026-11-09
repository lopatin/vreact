// expect: verified
// Calls of @opaque functions under a binder of the goal: their contracts are instantiated once the
// binder is opened (`vreact_open`). The timer's update calls `bump` through a transparent reducer
// (the step-34 shape of the options-chain feed), a functional update calls it directly (timer,
// continuous handler, rebase-checked click and child callback), and `map`/`every` lambdas call
// `clamp`, also nested.
import { useReducer, useState, useEffect } from "react";
import { ensures, implies, invariant, type int } from "vreact/spec";
type S = { readonly n: int; readonly m: int; readonly paused: boolean };
type A = { readonly kind: "tick" } | { readonly kind: "inc" } | { readonly kind: "pause" };
export function ok(n: int): boolean {
  return 0 <= n && n <= 10;
}
/** @opaque */
export function bump(n: int): int {
  ensures((r: int) => implies(ok(n), ok(r)));
  return n < 10 ? n + 1 : 0;
}
export function step(s: S, a: A): S {
  switch (a.kind) {
    case "tick":
      return s.paused ? s : { ...s, m: bump(s.m) };
    case "inc":
      return { ...s, n: bump(s.n) };
    case "pause":
      return { ...s, paused: !s.paused };
  }
}
type ChildProps = { readonly onInc: () => void };
export function Child(props: ChildProps) {
  return <button onClick={() => props.onInc()}>+</button>;
}
export function Ticker() {
  const [s, dispatch] = useReducer(step, { n: 0, m: 0, paused: false });
  invariant(ok(s.n) && ok(s.m));
  useEffect(() => {
    const id = setInterval(() => dispatch({ kind: "tick" }), 1000);
    return () => clearInterval(id);
  }, []);
  return (
    <div>
      <button onClick={() => dispatch({ kind: "inc" })}>{s.n}</button>
      <button onClick={() => dispatch({ kind: "pause" })}>{s.m}</button>
      <Child onInc={() => dispatch({ kind: "inc" })} />
    </div>
  );
}
export function Mover() {
  const [n, setN] = useState<int>(0);
  invariant(ok(n));
  useEffect(() => {
    const id = setInterval(() => setN((p) => bump(p)), 1000);
    return () => clearInterval(id);
  }, []);
  return (
    <div onMouseMove={() => setN((p) => bump(p))}>
      <button onClick={() => setN((p) => bump(p))}>{n}</button>
    </div>
  );
}
/** @opaque */
export function clamp(x: int): int {
  ensures((r: int) => 0 <= r && r <= 9);
  return x < 0 ? 0 : x > 9 ? 9 : x;
}
export function clampAll(xs: readonly int[]): int[] {
  ensures((r: int[]) => r.every((y) => 0 <= y));
  return xs.map((x) => clamp(x));
}
export function allClamped(xs: readonly int[]): boolean {
  ensures((r: boolean) => r);
  return xs.every((x) => clamp(x) <= 9);
}
export function nested(xs: readonly int[]): int[] {
  ensures((r: int[]) => r.length === xs.length && r.every((y) => 0 <= y && y <= 9));
  return xs.map((x) => clamp(clamp(x) + 1));
}
export function Clamped() {
  const [xs, setXs] = useState<readonly int[]>([]);
  invariant(xs.length <= 5 && xs.every((x) => 0 <= x && x <= 9));
  return <button onClick={() => setXs(xs.map((x) => clamp(x + 1)))}>{xs.length}</button>;
}
