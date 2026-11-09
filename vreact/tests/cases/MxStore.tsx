// expect: verified errors=none
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type Item = { readonly id: int; readonly label: string };

function Count(props: { readonly counts: ReadonlyMap<string, int>; readonly name: string }) {
  const c = props.counts.get(props.name) ?? 0;
  return <li>{props.name}: {c}</li>;
}

// a Map in state keyed by the items' ids, rendered by its values (keys: the ids, distinct by the
// invariant), updated by copy-then-mutate in a functional update; a Map built in render
export function Store() {
  const [items, setItems] = useState<ReadonlyMap<int, Item>>(new Map());
  invariant([...items.entries()].every(([k, it]) => k === it.id));
  const counts = new Map<string, int>();
  for (const it of items.values()) counts.set(it.label, (counts.get(it.label) ?? 0) + 1);
  const add = (id: int, label: string) =>
    setItems((prev) => {
      const n = new Map(prev);
      n.set(id, { id, label });
      return n;
    });
  const remove = (id: int) =>
    setItems((prev) => {
      const n = new Map(prev);
      n.delete(id);
      return n;
    });
  return (
    <div>
      <ul>
        {[...items.values()].map((it) => (
          <li key={it.id} onClick={() => remove(it.id)}>{it.label}</li>
        ))}
      </ul>
      <ul>
        {[...counts.entries()].map(([name, k]) => <Count key={name} counts={counts} name={name} />)}
      </ul>
      <button onClick={() => add(items.size + 1, "new")}>add</button>
      <p>{items.get(1)?.label ?? "none"}</p>
    </div>
  );
}
