// expect: fail nonzero-divisor postcondition f=incomplete f2=incomplete g=incomplete
// JS evaluates the case labels in the order written, the labels grouped with `default` included
// (`case X: default:`, `default: case X:`), until one matches, and takes `default` only when none
// does. The default group's labels used to be dropped: f was VERIFIED with no obligation although
// f(2, 0) throws "idiv by zero", and g's false postcondition was proved (for k = j = 1 the label 1
// of the default group matches first, so g returns 0 and `case j` is never tested).
import { ensures, idiv, implies, type int } from "vreact/spec";
export function f(k: int, d: int): int {
  switch (k) {
    case 1:
      return 10;
    case idiv(10, d):
    default:
      return 0;
  }
}
export function f2(k: int, d: int): int {
  switch (k) {
    case 1:
      return 10;
    default:
    case idiv(10, d):
      return 0;
    case 2:
      return 20;
  }
}
export function g(k: int, j: int): int {
  ensures((r: int) => implies(k === j, r === 5));
  switch (k) {
    case 1:
    default:
      return 0;
    case j:
      return 5;
  }
}
