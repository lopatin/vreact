// expect: reject which is reassigned after the function is created
// The contracts of a @trusted function are translated (its axioms) although its body is not, so
// closures in them must agree with JS, as in a verified body.  In JS the every callback is true
// (g reads the latest y, 2); the translation would read y as 1, making the axiom five.post False,
// and one() (which returns 6 in JS) would be VERIFIED against r === 1.
import { ensures, type int } from "vreact/spec";

/** @trusted */
export function five(): int {
  ensures((r: int) =>
    [r].every((x) => {
      let y = 1;
      const g = () => y;
      y = 2;
      return g() === 2;
    }),
  );
  return 5;
}

export function one(): int {
  ensures((r: int) => r === 1);
  const z = five();
  return z + 1;
}
