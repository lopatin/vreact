// expect: reject this function reads `step`, which is reassigned after the function is created
// A handler reads a `let` declared after it that is reassigned after the handler is attached: JS
// runs the handler with step = -4, not 2. closureEnv binds a later local from the attach site
// (with its value there, 2), which is sound only because checkClosures rejects every assignment
// of such a `let` (each comes after the function); this case pins that precondition, so that
// narrowing checkClosures to lets declared before the function cannot go unnoticed.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function C() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const inc = () => setN(n + step);
  let step: int = 2;
  const el = <button onClick={inc}>{n}</button>;
  step--;
  step -= 5;
  return el;
}
