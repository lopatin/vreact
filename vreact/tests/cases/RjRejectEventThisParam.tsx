// expect: reject a `this` parameter is not supported
// TypeScript's `this` parameter is not a parameter: binding it as the event (or, in a
// callback, as the first argument) shifts every later parameter by one.
import { useState } from "react";

export function RjEventThisParam() {
  const [s, setS] = useState<string>("");
  return (
    <div>
      <input onKeyDown={function (this: void) { setS("k"); }} />
      <p>{s.length}</p>
    </div>
  );
}
