// expect: status verdict=not-verified errors=build twice=verified Counter=unchecked proved=1 unchecked=4
// proofs/Counter.lean imports a module that does not exist: lake reports it without a
// line:col. The error must be shown, and the obligations of View.lean (which imports the
// proof file and so is never elaborated) must not count as proved.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { twice } from "./model";
export function Counter() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(twice(n) + 1)}>{n}</button>;
}
