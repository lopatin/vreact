// expect: reject which is reassigned after the function is created
// A handler-local helper called after its `let` is reassigned reads the new value in JS (2):
// the translation must not evaluate it with the old one (1).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function TrLetInHandler() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 1);
  return (
    <button
      onClick={() => {
        let x: int = 1;
        const f = () => x;
        x = 2;
        setN(f());
      }}
    >
      {n}
    </button>
  );
}
