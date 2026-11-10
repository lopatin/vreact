// expect: reject which is reassigned after the function is created
// A module-level constant's initialiser is translated (its Lean definition), so closures in it
// must agree with JS, as in a function body.  In JS OK is true (g reads the latest y, 2), the
// translation's OK would be false, and f (which returns 2 in JS) would be VERIFIED against r === 1.
import { ensures, type int } from "vreact/spec";

export const OK: boolean = [1].every((x) => {
  let y = 1;
  const g = () => y;
  y = 2;
  return g() === 2;
});

export function f(): int {
  ensures((r: int) => r === 1);
  return OK ? 2 : 1;
}
