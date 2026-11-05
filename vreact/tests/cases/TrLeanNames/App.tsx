// expect: verified verdict=verified Type=verified Prop=verified Nat=verified List=verified E=verified Props=verified VTS=verified App=verified errors=none
// Components and modules whose names are Lean keywords or Lean names (Type, Prop, List, …;
// modules at.ts, end/Sort.tsx, open/Type.tsx; proofs in proofs/end_/Sort_.lean) are renamed
// in Lean, everywhere they are emitted.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { at } from "./at";
import { Sort } from "./end/Sort";
import { Option } from "./open/Type";

export function Type(props: { readonly n: int }) {
  return <p>{at(props.n)}</p>;
}

export function Prop() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <div><button onClick={() => setN(n + 1)}>+</button><Type n={n} /></div>;
}

export function Nat() {
  return <Prop />;
}

export function List() {
  return <div><Nat /><Sort /><Option k={1} /></div>;
}

export function E() {
  return <List />;
}

export function Props() {
  return <E />;
}

export function VTS() {
  return <Props />;
}

export function App() {
  return <VTS />;
}
