// expect: verified C=verified Lazy=verified Red=verified
// A useState / useReducer initial value may read a state value declared before it: React
// evaluates it in the render and uses it at mount, when that state is its own initial value
// (formerly rejected: "unknown or unsupported identifier `a` (only locals, props, state, …)").
import { useState, useReducer } from "react";
import { invariant, type int } from "vreact/spec";
export function C() {
  const [a, setA] = useState<int>(5);
  const [b, setB] = useState<int>(a);
  invariant(a === b);
  return <button onClick={() => { setA(a + 1); setB(b + 1); }}>{a}{b}</button>;
}
// a lazy initialiser runs at mount only: 10 % a is never evaluated with another a
export function Lazy() {
  const [a, setA] = useState<int>(5);
  const [b] = useState<int>(() => 10 % a);
  invariant(b === 0);
  return <button onClick={() => setA(0)}>{a}{b}</button>;
}
function step(s: int, d: int): int {
  return s + d;
}
export function Red(props: { readonly start: int }) {
  const [a] = useState<int>(props.start > 0 ? props.start : 1);
  const [s, dispatch] = useReducer(step, a + 1);
  invariant(s >= 2 || s < 2);
  return <button onClick={() => dispatch(1)}>{a}{s}</button>;
}
