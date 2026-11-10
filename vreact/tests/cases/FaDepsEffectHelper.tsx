// expect: verified
// An effect that depends on a local helper arrow (a new function at every render: the effect
// runs after every render, as in React), or on a setter / dispatch (React keeps one function per
// hook: it never changes). Before, `[bump]` was refused as a function value and `[setN]` with
// the false reason that setters may only be called in handlers and effects.
import { useState, useEffect, useReducer } from "react";
import { invariant, type int } from "vreact/spec";

type Action = { readonly kind: "inc" } | { readonly kind: "reset" };
function reducer(s: int, a: Action): int {
  switch (a.kind) {
    case "inc":
      return s + 1;
    case "reset":
      return 0;
  }
}

export function FaDepsEffectHelper() {
  const [n, setN] = useState<int>(0);
  const [r, dispatch] = useReducer(reducer, 0);
  invariant(n >= 0);
  invariant(r >= 0);
  const bump = () => setN((p) => p + 1);
  useEffect(() => {
    bump();
  }, [bump]);
  useEffect(() => {
    setN((p) => p + 1);
  }, [setN]);
  useEffect(() => {
    dispatch({ kind: "inc" });
  }, [dispatch]);
  return <p>{n + r}</p>;
}
