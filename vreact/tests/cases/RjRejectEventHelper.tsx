// expect: reject is read inside a function created in the handler
// A helper created in the handler may run later; read the event in the handler and copy it.
import { useState } from "react";
import { invariant } from "vreact/spec";
export function RjEventHelper() {
  const [s, setS] = useState<string>("");
  invariant(s.length >= 0);
  return (
    <input value={s} onKeyDown={(e) => {
      const key = () => e.key;
      setS(key());
    }} />
  );
}
