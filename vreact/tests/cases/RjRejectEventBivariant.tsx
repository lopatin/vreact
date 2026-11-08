// expect: reject is not a string in onClick on <div>
// React's handler types are bivariant (`bivarianceHack`), so TypeScript accepts a handler
// annotated for an <input> as a <div>'s onClick and types `e.currentTarget.value` as a
// string; but currentTarget is the <div>, whose value is undefined: setS(undefined), and the
// next render's `s.length` throws a TypeError.
import { useState, type MouseEvent } from "react";
import { invariant } from "vreact/spec";
export function RjEventBivariant() {
  const [s, setS] = useState<string>("");
  invariant(s.length >= 0);
  return (
    <div onClick={(e: MouseEvent<HTMLInputElement>) => setS(e.currentTarget.value)}>
      {s.length}
    </div>
  );
}
