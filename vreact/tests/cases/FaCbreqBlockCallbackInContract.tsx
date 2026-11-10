// expect: verified
// An expression-bodied callbackRequires lambda is read as a contract, and inside it an array
// callback that `(x) => condition` does not cover — a block body `(x) => { return c; }`, a
// `function (x) { … }` — is read as code (as it was before the lambda became a contract; the
// contract reading had rejected it with "some((x) => condition) with an expression body"). JS
// calls such a callback on each element, so the code reading is its meaning. The parent relies
// on a contract written that way.
import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";

type It = { readonly id: int; readonly name: string };

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

type DP = { readonly items: readonly It[]; readonly onPick: (id: int) => void };
export function Every(props: DP) {
  callbackRequires(props.onPick, (id) => props.items.every((it) => { return it.id !== id || it.name !== ""; }));
  return (
    <button
      onClick={() => {
        if (props.items.every((it) => { return it.id !== 7 || it.name !== ""; })) props.onPick(7);
      }}
    >
      b
    </button>
  );
}

export function Fn(props: DP) {
  callbackRequires(props.onPick, (id) => id > 0 && props.items.some(function (it) { return it.id === id; }));
  return (
    <button
      onClick={() => {
        if (props.items.length > 0 && props.items[0].id > 0) props.onPick(props.items[0].id);
      }}
    >
      c
    </button>
  );
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <Child ids={[1, 2, 3]} onPick={(id) => setN(id)} />;
}
