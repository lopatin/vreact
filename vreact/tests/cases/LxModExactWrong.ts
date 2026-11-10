// expect: fail postcondition ok=verified
// False controls for the exact values of `%` (node: 5 % 5 === 0, -1 % 3 === -1, 4 % 3 === 1).
import { requires, ensures, type int } from "vreact/spec";

export function ok(n: int): int {
  requires(n > 0);
  ensures((r: int) => r === 0);
  return n % n;
}
// no upper bound on sel: wraps
export function noBound(sel: int, n: int): int {
  requires(n > 0 && 0 <= sel);
  ensures((r: int) => r === sel + 1);
  return (sel + 1) % n;
}
export function notOne(n: int): int {
  requires(n > 0);
  ensures((r: int) => r === 1);
  return n % n;
}
// Lean's Euclidean `emod` gives 2; JS gives -1
export function euclid(): int {
  ensures((r: int) => r === 2);
  return -1 % 3;
}
