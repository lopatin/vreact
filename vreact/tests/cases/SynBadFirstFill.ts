// expect: fail postcondition
// The first-hole fill that `vreact synth` used to report "proved by Lean" while the second hole was open.
import { requires, ensures, type int } from "vreact/spec";

export function bucket(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  if (x <= 100) return x;
  return 0;
}
