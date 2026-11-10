// expect: reject which is reassigned after the function is created
// A module-level assert(…) is translated (a theorem that callers may use), so closures in it must
// agree with JS.  The translation would read y as x (N, which is 5) and prove the fact, which is
// false in JS (g reads the latest y, 0).
import { assert, type int } from "vreact/spec";

/** @opaque */
export const N: int = 5;
assert(
  [N].every((x) => {
    let y = x;
    const g = () => y;
    y = 0;
    return g() === 5;
  }),
);
