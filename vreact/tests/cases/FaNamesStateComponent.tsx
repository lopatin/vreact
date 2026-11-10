// expect: verified Timer=verified
// The inline record type of the state `timer` is named after it (`Timer`), which is also the
// namespace of the component Timer (its Props, State, init, …): with the field `init` the two
// met (`invalid declaration name init`); the type now gets a fresh name.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Timer() {
  const [timer, setTimer] = useState<{ readonly init: int; readonly left: int }>({ init: 10, left: 10 });
  invariant(timer.left >= 0);
  return <button onClick={() => setTimer({ init: timer.init, left: 10 })}>{timer.left}</button>;
}
