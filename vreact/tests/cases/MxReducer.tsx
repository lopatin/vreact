// expect: verified qtys=verified errors=none
import { useReducer, useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

type Action = { kind: "put"; id: int; qty: int } | { kind: "drop"; id: int } | { kind: "reset" };
type Ui = { readonly held: ReadonlyMap<int, int>; readonly open: ReadonlySet<string> };

// a reducer over a Map state
export function qtys(s: ReadonlyMap<int, int>, a: Action): ReadonlyMap<int, int> {
  ensures((r) => a.kind !== "drop" || !r.has(a.id));
  switch (a.kind) {
    case "put": {
      if (a.qty < 0) return s;
      const n = new Map(s);
      n.set(a.id, a.qty);
      return n;
    }
    case "drop": {
      const n = new Map(s);
      n.delete(a.id);
      return n;
    }
    case "reset":
      return new Map<int, int>();
  }
}

// records with Map/Set fields, updated with pure chains on fresh copies
export function Shop() {
  const [q, dispatch] = useReducer(qtys, new Map<int, int>());
  const [ui, setUi] = useState<Ui>({ held: new Map(), open: new Set() });
  invariant([...q.values()].every((x) => x >= 0));
  invariant([...ui.held.values()].every((x) => x > 0));
  return (
    <div>
      <button onClick={() => dispatch({ kind: "put", id: 1, qty: 2 })}>put</button>
      <button onClick={() => dispatch({ kind: "drop", id: 1 })}>drop</button>
      <button onClick={() => setUi({ ...ui, held: new Map(ui.held).set(q.size, 1 + (q.get(1) ?? 0)) })}>hold</button>
      <button onClick={() => setUi({ ...ui, open: new Set(ui.open).add("a") })}>open</button>
      <p>{q.get(1) ?? 0} {ui.open.size} {ui.held.size}</p>
    </div>
  );
}
