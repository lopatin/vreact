// expect: fail postcondition
// The accepted shape still proves only true facts: f(true) is 1, not null.
import { ensures, implies, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(b: boolean): int | null {
  ensures((r) => isNull(r));
  return b ? 1 : null;
}
