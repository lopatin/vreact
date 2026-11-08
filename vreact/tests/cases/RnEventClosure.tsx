// expect: verified
// A local closure used as an event handler takes the event, which is not data and is not inlined
// as an argument: its annotation (`ChangeEvent<…>`) is not a VTS value type and need not be. A
// helper called with data arguments is inlined with them (`bump(1)`).
import { useState, type ChangeEvent } from "react";
import { type int, invariant } from "vreact/spec";

export function App() {
  const [text, setText] = useState<string>("");
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const onChange = (e: ChangeEvent<HTMLInputElement>) => setText(e.target.value);
  const bump = (k: int): void => setN(n + k);
  return (
    <div>
      <input value={text} onChange={onChange} />
      <button onClick={() => bump(1)}>{n}</button>
    </div>
  );
}
