// expect: status A=incomplete B=incomplete why.A=not~checked why.B=not~checked uncheckedwhy=hole()
// A hole() in a component's invariant (or its initial state) is unfinished code, not a
// counterexample: the obligations that fail on it are not checked (blocked), like those
// through a function's hole, since the automation unfolds `inv` and `init` (@[vreact_simp])
// (formerly the init-invariant obligation was reported failed, `h : sorry = false ⊢ False`).
import { useState } from "react";
import { invariant, hole, type int } from "vreact/spec";

export function A() {
  const [n, setN] = useState<int>(0);
  invariant(hole<boolean>());
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}

export function B() {
  const [n, setN] = useState<int>(hole<int>());
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
