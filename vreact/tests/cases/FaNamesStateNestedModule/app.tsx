// expect: verified verdict=verified App=verified errors=none
// The inline record type of the state `timer` would be named `Timer`, which is the namespace of the
// nested module src/app/Timer.ts (VTS.app.Timer, with its function VTS.app.Timer.left, the type's
// field `left`): the type gets a fresh name (it was rejected as a name clash asking to rename a
// declaration `Timer` the module does not have).
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function App() {
  const [timer, setTimer] = useState<{ readonly left: int }>({ left: 10 });
  invariant(timer.left >= 0);
  return <button onClick={() => setTimer({ left: 10 })}>{timer.left}</button>;
}
