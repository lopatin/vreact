// expect: verified
// V1 (regression of round 3): a precondition that is a single guarded part (an `exists`, an `||`
// with an indexed `&&`, an `every` with an indexed body) and its copy made by `vreact_expose` must
// not each be dropped as a duplicate of the other: the postconditions below need the precondition.
import { requires, ensures, exists, type int } from "vreact/spec";

export function exLen(xs: readonly int[]): int {
  requires(exists(0, xs.length, (i) => xs[i] < 0));
  ensures((r: int) => r > 0);
  return xs.length;
}
export function exSome(xs: readonly int[]): boolean {
  requires(exists(0, xs.length, (i) => xs[i] < 0));
  ensures((b: boolean) => b === true);
  return xs.some((x) => x < 0);
}
export function head(xs: readonly int[], dflt: int): int {
  requires((xs.length > 0 && xs[0] >= 0) || dflt >= 0);
  ensures((r: int) => r >= 0 || xs.length > 0);
  return xs.length > 0 ? xs[0] : dflt;
}
export function orGuard(flag: boolean, xs: readonly int[]): int {
  requires(flag || (xs.length > 0 && xs[0] > 1));
  ensures((r: int) => flag || r > 1);
  return xs.length > 0 ? xs[0] : 5;
}
export function everyHead(xss: readonly (readonly int[])[]): boolean {
  requires(xss.every((x) => x.length > 0 && x[0] > 0));
  ensures((b: boolean) => b === true);
  return xss.every((x) => x.length > 0);
}
// the body indexes with the precondition (the goal depends on it)
export function exHead(xs: readonly int[]): int {
  requires(exists(0, xs.length, (i) => xs[i] < 0));
  ensures((r: int) => r === xs[0]);
  return xs[0];
}
