// expect: verified OPEN=verified CLOSE=verified after=verified
// The source text of a module-level fact goes into a Lean doc comment; Lean comments nest
// and end at `-/`, so a fact mentioning "-/" or "/-" must not end or open a comment (before:
// the doc comment swallowed the rest of Defs.lean, and nothing in the module was checked).
import { assert, ensures, type int } from "vreact/spec";
/** @opaque */
export const CLOSE: string = "a-/b";
assert(CLOSE !== "-/");
/** @opaque */
export const OPEN: string = "/-";
assert(OPEN !== "x/-y" && OPEN.length === 2);
export function after(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
