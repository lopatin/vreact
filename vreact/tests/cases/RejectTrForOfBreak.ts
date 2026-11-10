// expect: reject a `break` may only end a switch case
// A break that leaves the loop (here: from an if inside a switch case's loop) is still rejected.
import { type int } from "vreact/spec";
export function firstBig(xs: readonly int[]): int {
  let s: int = 0;
  for (const x of xs) {
    switch (x) {
      case 0:
        s += 1;
        break;
      default:
        for (const y of xs) {
          if (y > x) break;
          s += y;
        }
        break;
    }
  }
  return s;
}
