// expect: fail index non-null precondition
// The same with obligations that do not hold: they are reported (formerly they vanished with the
// operand, an internal error "obligation … is missing from the generated Lean").
import { ensures, requires, type int } from "vreact/spec";
export function g(x: int): int {
  requires(x > 0);
  return x;
}
export function a(xs: readonly int[]): boolean {
  ensures((r: boolean) => r === false);
  return xs[5] === null;
}
export function b(): boolean {
  ensures((r: boolean) => r === true);
  return g(-1) != null;
}
export function c(x: int | null): boolean {
  return x! === null;
}
export function d(n: int): int {
  ensures((r: int) => g(-1) !== null);
  return n;
}
