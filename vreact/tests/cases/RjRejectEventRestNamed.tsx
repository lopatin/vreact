// expect: reject a rest parameter `...args` of the local function onKey is not supported
// The same through a local handler passed by name: a rest parameter collects the arguments
// into an array, so `args.key` is undefined in JS.
import { useState, type KeyboardEvent } from "react";

export function RjEventRestNamed() {
  const [s, setS] = useState<string>("");
  const onKey = (...args: [KeyboardEvent<HTMLInputElement>] & { key: string }) => setS(args.key);
  return (
    <div>
      <input onKeyDown={onKey} />
      <p>{s.length}</p>
    </div>
  );
}
