// expect: reject prop items has the function type () => void (field onPick of Item), which is not data
// A Map of records with a callback field as a data prop: rejected like `readonly Item[]` (the
// generated Lean failed with "Unknown identifier `VTS.List_.Item`" before).
import { useState } from "react";
import { type int } from "vreact/spec";

type Item = { readonly id: int; readonly label: string; readonly onPick: () => void };

export function List(props: { readonly items: ReadonlyMap<int, Item> }) {
  const [n, setN] = useState<int>(0);
  return <button onClick={() => setN(props.items.size)}>{n}</button>;
}
