// expect: verified
// A transparent reducer over a discriminated union whose arms pass payload fields to
// @opaque functions: their contracts must be instantiated inside the match arms.
import { useReducer } from "react";
import { ensures, implies, invariant, type int } from "vreact/spec";
type S = { readonly n: int; readonly max: int };
type A = { readonly kind: "add"; readonly by: int } | { readonly kind: "reset" };

export function ok(s: S): boolean {
  return 0 <= s.n && s.n <= s.max;
}
/** @opaque */
export function add(s: S, by: int): S {
  ensures((r: S) => implies(ok(s), ok(r)));
  if (by < 0 || s.n + by > s.max) return s;
  return { ...s, n: s.n + by };
}
/** @opaque */
export function reset(s: S): S {
  ensures((r: S) => implies(ok(s), ok(r)));
  return { ...s, n: 0 };
}
export function step(s: S, a: A): S {
  ensures((r: S) => implies(ok(s), ok(r)));
  switch (a.kind) {
    case "add":
      return add(s, a.by);
    case "reset":
      return reset(s);
  }
}
export function Stepper() {
  const [s, dispatch] = useReducer(step, { n: 0, max: 10 });
  invariant(ok(s));
  return (
    <div>
      <button onClick={() => dispatch({ kind: "add", by: 3 })}>+3</button>
      <button onClick={() => dispatch({ kind: "reset" })}>reset</button>
      {s.n}
    </div>
  );
}
