// expect: fail postcondition
// After `x = 5` inside `if (x !== null)`, x is 5, not the narrowed old value (p).
import { ensures, type int } from "vreact/spec";

export function stale(p: int | null): int {
  ensures((r: int) => r === (p ?? 0));
  let x: int | null = p;
  if (x !== null) {
    x = 5;
    return x;
  }
  return 0;
}
