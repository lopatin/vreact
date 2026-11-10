// expect: verified C=verified Chain=verified
// A local handler may read a const declared after it: React calls the handler after the render,
// when the const is initialised (formerly rejected: "unknown or unsupported identifier `step`",
// false, since `step` is a local). The handler is translated where it is attached, with the
// locals declared after it that are initialised there; `Chain`: through a second closure.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const inc = () => setN(n + step);
  const step: int = 2;
  return <button onClick={inc}>{n}</button>;
}

export function Chain(props: { readonly big: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const by = (k: int): int => k + step;
  const inc = () => setN(by(n));
  const step: int = props.big ? 10 : 1;
  return <button onClick={inc}>{n}</button>;
}
