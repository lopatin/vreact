// expect: verified
// The labels of the default group are tested at their place: their obligations are under the
// negation of the labels before them, and a later label is evaluated only when they do not match
// (`lazy` and `mid` were spurious [index]/[postcondition] failures). The discriminant is evaluated
// once, also when no label mentions it (`h`, `only`: formerly "missing from the generated Lean").
import { ensures, idiv, implies, requires, type int } from "vreact/spec";
export function f(k: int, d: int): int {
  requires(k === 1 || d !== 0);
  switch (k) {
    case 1:
      return 10;
    case idiv(10, d):
    default:
      return 0;
  }
}
export function lazy(k: int, xs: readonly int[]): int {
  requires(k === 1 || k === 5 || xs.length > 0);
  ensures((r: int) => implies(k === 5, r === 0));
  switch (k) {
    case 1:
      return 1;
    case 5:
    default:
      return 0;
    case xs[0]:
      return 2;
  }
}
export function mid(k: int, xs: readonly int[]): int {
  requires(k === 0 || xs.length > 0);
  ensures((r: int) => implies(k === 0, r === 1) && implies(k === 7 && xs.length > 0 && xs[0] !== 7, r === 2));
  switch (k) {
    case 0:
      return 1;
    default:
    case xs[0]:
      return 0;
    case 7:
      return 2;
  }
}
export function g(k: int, j: int): int {
  ensures((r: int) => implies(k === 1, r === 0) && implies(k !== 1 && k === j, r === 5));
  switch (k) {
    case 1:
    default:
      return 0;
    case j:
      return 5;
  }
}
export function h(d: int): int {
  requires(d !== 0);
  switch (idiv(10, d)) {
    case 5:
    default:
      return 0;
  }
}
export function only(d: int): int {
  requires(d !== 0);
  ensures((r: int) => r === 1);
  switch (idiv(10, d)) {
    default:
      return 1;
  }
}
