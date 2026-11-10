// expect: verified Before=verified Between=verified Twice=verified
// Each state value and setter is bound at its own declaration (no longer for the whole body),
// and what JS allows still verifies. `Before`: a handler created before the useState it reads,
// attached after it (React calls it after the render, when `n` and `setN` are initialised).
// `Between`: render locals between hooks, reading the props and the state declared before them.
// `Twice`: a helper called several times, nested, and a handler called twice (not recursion).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Before() {
  const inc = () => setN(n + 1);
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={inc}>{n}</button>;
}

export function Between(props: { readonly k: int }) {
  const step: int = props.k > 0 ? props.k : 1;
  const [n, setN] = useState<int>(0);
  const label: string = n > 0 ? "pos" : "zero";
  const [m, setM] = useState<int>(0);
  invariant(n >= 0 && m >= 0);
  return <button onClick={() => { setN(n + step); setM(m + 1); }}>{label}{m}</button>;
}

export function Twice() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const inc = () => setN((k) => k + 1);
  const two = (k: int): int => k + 2;
  return <button onClick={() => { inc(); inc(); setN(two(two(n))); }}>{n}</button>;
}
