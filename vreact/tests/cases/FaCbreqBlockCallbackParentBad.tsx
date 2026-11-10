// expect: fail callback
// The parent assumes exactly the child's contract `props.ids.some((x) => { return x === id; })`
// (read as code), nothing stronger: id may be 1, which breaks the parent's n >= 2.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type CP = { readonly ids: readonly int[]; readonly onPick: (id: int) => void };
export function Child(props: CP) {
  callbackRequires(props.onPick, (id) => props.ids.some((x) => { return x === id; }));
  return (
    <button
      onClick={() => {
        if (props.ids.length > 0) props.onPick(props.ids[0]);
      }}
    >
      a
    </button>
  );
}

export function App() {
  const [n, setN] = useState<int>(2);
  invariant(n >= 2);
  return <Child ids={[1, 2, 3]} onPick={(id) => setN(id)} />;
}
