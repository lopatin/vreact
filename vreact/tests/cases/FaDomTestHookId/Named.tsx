import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { next } from "./M";

// The id comes from what the user types: typing __VREACT_TEST__ made next(n) throw.
export function Named() {
  const [name, setName] = useState<string>("");
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return (
    <div>
      <input value={name} onChange={(e) => setName(e.target.value)} />
      <h2 id={name}>{name}</h2>
      <button onClick={() => setN(next(n))}>{n}</button>
    </div>
  );
}
