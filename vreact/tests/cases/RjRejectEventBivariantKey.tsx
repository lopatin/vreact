// expect: reject only keyboard events (onKeyDown, onKeyUp, onKeyPress) have a key
// A keyboard handler accepted as a <div>'s onChange (bivariant handler types): the change
// event bubbling from the <input> has no `key`, so `e.key` is undefined.
import { useState, type KeyboardEvent } from "react";
import { invariant } from "vreact/spec";
export function RjEventBivariantKey() {
  const [s, setS] = useState<string>("");
  invariant(s.length >= 0);
  return (
    <div onChange={(e: KeyboardEvent<HTMLDivElement>) => setS(e.key)}>
      <input />
      {s.length}
    </div>
  );
}
