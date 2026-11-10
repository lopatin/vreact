// expect: verified
import { useReducer } from "react";
import { ensures, requires, invariant, type int } from "vreact/spec";

// a value read with get is its key's entry: toggling a field of s.get(id) keeps the key/id invariant
export type MxgeItem = { readonly id: int; readonly title: string; readonly done: boolean };
export type MxgeAction = { kind: "toggle"; id: int } | { kind: "rename"; id: int; title: string };

export function mxgeKeyed(s: ReadonlyMap<int, MxgeItem>): boolean {
  return [...s.entries()].every(([k, v]) => k === v.id);
}

export function mxgeStep(s: ReadonlyMap<int, MxgeItem>, a: MxgeAction): ReadonlyMap<int, MxgeItem> {
  ensures((r) => !mxgeKeyed(s) || mxgeKeyed(r));
  ensures((r) => r.size === s.size);
  switch (a.kind) {
    case "toggle": {
      const it = s.get(a.id);
      if (it === undefined) return s;
      return new Map(s).set(a.id, { ...it, done: !it.done });
    }
    case "rename": {
      const it = s.get(a.id);
      if (it === undefined) return s;
      return new Map(s).set(a.id, { ...it, title: a.title });
    }
  }
}

export function mxgeIdOf(s: ReadonlyMap<int, MxgeItem>, id: int): int {
  requires([...s.entries()].every(([k, v]) => k === v.id));
  requires(s.has(id));
  ensures((r) => r === id);
  return s.get(id)!.id;
}

export function MxGetEntry() {
  const [s, dispatch] = useReducer(mxgeStep, new Map<int, MxgeItem>([[1, { id: 1, title: "a", done: false }], [2, { id: 2, title: "b", done: true }]]));
  invariant(mxgeKeyed(s));
  invariant(s.size === 2);
  return (
    <ul>
      {[...s.values()].map((it) => (
        <li key={it.id} onClick={() => dispatch({ kind: "toggle", id: it.id })}>
          {it.title}
        </li>
      ))}
    </ul>
  );
}
