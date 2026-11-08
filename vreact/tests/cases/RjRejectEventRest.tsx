// expect: reject a rest parameter `...e` is the array of the handler's arguments
// A rest parameter on a DOM handler is the array of its arguments, [event]: `e.key` is
// undefined in JS (setS(undefined), then s.length throws), but binding `e` as the event modelled
// it as the key. TypeScript accepts it (React's handler types are bivariant).
import { useState, type KeyboardEvent } from "react";

export function RjEventRest() {
  const [s, setS] = useState<string>("");
  return (
    <div>
      <input onKeyDown={(...e: [KeyboardEvent<HTMLInputElement>] & { key: string }) => setS(e.key)} />
      <p>{s.length}</p>
    </div>
  );
}
