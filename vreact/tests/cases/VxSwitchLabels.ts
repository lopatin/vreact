// expect: verified
// switch labels on a primitive value: normalised literals (0x10, 1e2), negative and -0 (=== 0)
// labels, constants, large literals; strings, booleans; numbers (IEEE ===); a repeated label
// (-0 after 0) is never taken.
import { ensures, implies, type int } from "vreact/spec";
const LIMIT: int = 7;
const NAME = "bob";
export function h(n: int): int {
  ensures((r: int) => implies(n === 16, r === 1) && implies(n === 100, r === 2) && implies(n === -3, r === 3) && implies(n === 0, r === 4) && implies(n === 7, r === 5));
  switch (n) {
    case 0x10:
      return 1;
    case 1e2:
      return 2;
    case -3:
      return 3;
    case -0:
      return 4;
    case LIMIT:
      return 5;
    case 1e21:
      return 6;
    default:
      return 0;
  }
}
export function dup(n: int): int {
  ensures((r: int) => implies(n === 0, r === 1));
  switch (n) {
    case 0:
      return 1;
    case -0:
      return 2;
    default:
      return 0;
  }
}
export function s(x: string): int {
  ensures((r: int) => implies(x === "bob", r === 1));
  switch (x) {
    case NAME:
      return 1;
    default:
      return 0;
  }
}
export function b(x: boolean): int {
  ensures((r: int) => implies(x, r === 1));
  switch (x) {
    case true:
      return 1;
    default:
      return 0;
  }
}
export function num(n: number): int {
  switch (n) {
    case 1.5:
      return 3;
    case -2:
      return 2;
    default:
      return 0;
  }
}
