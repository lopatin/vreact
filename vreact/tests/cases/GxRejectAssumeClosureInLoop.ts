// expect: reject assume(…) is not supported in a for…of loop body
// A helper arrow is inlined where it is called: called from a for…of body, its assume(…) is
// checked there, for every element (no membership), so it is rejected as if written in the loop.
import { requires, assume, type int } from "vreact/spec";

export function total(xs: readonly int[]): int {
  requires(xs.every((x) => x > 0));
  const pos = (v: int): int => {
    assume(v > 0);
    return v;
  };
  let s = 0;
  for (const x of xs) {
    s = s + pos(x);
  }
  return s;
}
