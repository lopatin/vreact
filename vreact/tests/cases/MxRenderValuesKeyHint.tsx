// expect: fail unique-keys faildesc=for~the~values~of~a~Map:~key~by~the~Map~key
// Rendering a Map's values keyed by a field, without an invariant tying the field to the key:
// the failure says how to fix it (key by the Map key, or add [...m].every(([k, v]) => v.id === k)).
import { useState } from "react";
import { type int } from "vreact/spec";

type Item = { readonly id: int; readonly label: string };

export function Items() {
  const [items] = useState<ReadonlyMap<int, Item>>(new Map<int, Item>());
  return <ul>{[...items.values()].map((it) => <li key={it.id}>{it.label}</li>)}</ul>;
}
