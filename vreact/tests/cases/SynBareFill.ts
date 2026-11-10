// expect: fail postcondition
// The same fills pasted without parentheses (what `vreact synth` used to check and write).
import { requires, ensures, type int } from "vreact/spec";

export function total(base: int, qty: int): int {
  requires(qty >= 0);
  ensures((r: int) => r === (base + 1) * qty);
  return base + 1 * qty;
}

export function negSucc(x: int): int {
  ensures((r: int) => r === 0 - x - 1);
  return -x + 1;
}
