// expect: reject which is reassigned after the function is created
// The invariant of a @trusted component is translated (the axioms init_inv and stable state
// it), so closures in it must agree with JS.  In JS the every callback is true for every element
// (g reads the latest y, 2); the translation would read y as 1, so `inv` would be False and the
// axiom init_inv inconsistent.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

/** @trusted */
export function C() {
  const [xs, setXs] = useState<readonly int[]>([1]);
  invariant(
    xs.every((x) => {
      let y = 1;
      const g = () => y;
      y = 2;
      return g() === 2;
    }),
  );
  return <button onClick={() => setXs([2])}>c</button>;
}
