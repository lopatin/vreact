// expect: status get=assumes g=assumes f=trusted rel=relative plain=verified Show=assumes
// assume(…) is reported as ASSUMES (Lean prints the axiom `VReact.assumed` as `assumed`
// under `open VReact`), also when the function relies on a @trusted contract as well,
// and in a component that uses such a function.
import { assume, ensures, type int } from "vreact/spec";
export function get(xs: readonly int[], i: int): int {
  assume(0 <= i && i < xs.length);
  return xs[i];
}
/** @trusted */
export function f(x: int): int {
  ensures((r: int) => r >= 0);
  return x < 0 ? -x : x;
}
export function g(x: int): int {
  assume(x > 0);
  return f(x);
}
export function rel(x: int): int {
  return f(x) + 1;
}
export function plain(x: int): int {
  return x + 1;
}
export function Show() {
  return <p>{get([1, 2, 3], 0)}</p>;
}
