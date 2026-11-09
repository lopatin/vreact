// expect: verified TagPicker=verified toggleIn=verified countIn=verified
// A component's ReadonlySet<int> state updated with a generic helper in a functional updater,
// and a ReadonlyMap<string, int> state updated with a generic Map helper: the helpers' contracts
// (proved once for every K) give the invariants.
import { useState } from "react";
import { distinct, ensures, invariant, requires, type int } from "vreact/spec";

export function toggleIn<K extends int | string>(s: ReadonlySet<K>, k: K): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r.has(k) === !s.has(k));
  ensures((r: ReadonlySet<K>) => [...r].every((x) => x === k || s.has(x)));
  const n = new Set(s);
  if (n.has(k)) n.delete(k);
  else n.add(k);
  return n;
}

/** @opaque */
export function countIn<K extends int | string>(m: ReadonlyMap<K, int>, k: K): ReadonlyMap<K, int> {
  ensures((r: ReadonlyMap<K, int>) => [...m.keys()].every((x) => r.has(x)) && r.has(k));
  ensures((r: ReadonlyMap<K, int>) => ![...m.values()].every((v) => v >= 0) || [...r.values()].every((v) => v >= 0));
  return new Map(m).set(k, (m.get(k) ?? 0) + 1);
}

export function TagPicker(props: { readonly ids: readonly int[]; readonly label: string }) {
  requires(distinct(props.ids) && props.ids.every((i) => i >= 0));
  const [sel, setSel] = useState<ReadonlySet<int>>(new Set<int>());
  const [clicks, setClicks] = useState<ReadonlyMap<string, int>>(new Map<string, int>());
  invariant([...sel].every((x) => x >= 0));
  invariant([...clicks.values()].every((v) => v >= 0));
  return (
    <ul>
      {props.ids.map((id) => (
        <li key={id}>
          <input
            type="checkbox"
            checked={sel.has(id)}
            onChange={() => {
              setSel((s) => toggleIn(s, id));
              setClicks((m) => countIn(m, props.label));
            }}
          />
        </li>
      ))}
      <li>
        {sel.size} selected, {clicks.get(props.label) ?? 0} clicks
      </li>
    </ul>
  );
}
