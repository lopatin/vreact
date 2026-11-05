// expect: reject assigning it from inside a function or callback is not supported
// Writes to an outer `let` inside an array callback were dropped (JS returns xs.length).
import { ensures, type int } from "vreact/spec";
export function ctlCountViaMap(xs: readonly int[]): int {
  ensures((r: int) => r === 0);
  let n: int = 0;
  const ys = xs.map((y) => {
    n = n + 1;
    return y;
  });
  return n;
}
