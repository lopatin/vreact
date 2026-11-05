// expect: reject case 1.5 can never match: `n` is an int, and 1.5 is not an integer
// A non-integer label in a switch on an int (formerly non-compiling Lean).
import { ensures, implies, type int } from "vreact/spec";
export function h(n: int): int {
  ensures((r: int) => implies(n === 16, r === 1));
  switch (n) {
    case 0x10:
      return 1;
    case 1.5:
      return 3;
    default:
      return 0;
  }
}
