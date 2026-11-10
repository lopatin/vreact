// expect: fail effect-robust handler-robust postcondition
// The contracts instantiated under a binder are exactly the callee's: a contract too weak for the
// invariant (`bump` may leave 0..10) still fails the timer, the continuous handler and the
// postcondition over a `map` lambda.
import { useState, useEffect } from "react";
import { ensures, implies, invariant, type int } from "vreact/spec";
export function ok(n: int): boolean {
  return 0 <= n && n <= 10;
}
/** @opaque */
export function bump(n: int): int {
  ensures((r: int) => implies(ok(n), 0 <= r));
  return n < 10 ? n + 1 : 0;
}
export function Mover() {
  const [n, setN] = useState<int>(0);
  invariant(ok(n));
  useEffect(() => {
    const id = setInterval(() => setN((p) => bump(p)), 1000);
    return () => clearInterval(id);
  }, []);
  return <div onMouseMove={() => setN((p) => bump(p))}>{n}</div>;
}
export function bumpAll(xs: readonly int[]): int[] {
  ensures((r: int[]) => r.every((y) => y <= 10));
  return xs.map((x) => bump(x));
}
