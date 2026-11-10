// expect: reject `inc` reads `bump`, which is declared after it
// `inc` is attached in a JSX const declared before `bump`: VTS translates the handler there, where
// `bump` is not initialised (formerly "this call has no modelled effect: bump()", false).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const inc = () => bump();
  const el = <button onClick={inc}>{n}</button>;
  const bump = () => setN(n + 1);
  return el;
}
