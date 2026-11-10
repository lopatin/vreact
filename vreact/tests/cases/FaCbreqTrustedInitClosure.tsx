// expect: reject which is reassigned after the function is created
// The initial state of a @trusted component is translated (`init`, about which the axiom
// init_inv states the invariant), so closures in it must agree with JS as in a verified body.
// Here JS's initial state is true (g reads the latest y, 2), the translation's would be false
// (y as it was when g was created), and the axiom `inv (init)` would be False.
import { useState } from "react";
import { invariant } from "vreact/spec";

/** @trusted */
export function C() {
  const [ok, setOk] = useState<boolean>(() => {
    let y = 1;
    const g = () => y;
    y = 2;
    return g() === 2;
  });
  invariant(ok);
  return <button onClick={() => setOk(true)}>{ok ? "yes" : "no"}</button>;
}
