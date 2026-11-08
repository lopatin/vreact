// expect: verified Tags=verified toggleIn=verified countIn=verified
// Generic helpers in a component: instantiated at the component's state types in a handler, in
// the render and in the invariant (the @opaque toggleIn through its polymorphic contract).
import { useState } from "react";
import { ensures, invariant, distinct, type int } from "vreact/spec";

/** @opaque */
export function toggleIn<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.includes(k) === !xs.includes(k));
  ensures((r: readonly K[]) => !distinct(xs) || distinct(r));
  if (xs.includes(k)) return xs.filter((x) => x !== k);
  return [...xs, k];
}

export function countIn<K extends int | string>(xs: readonly K[], k: K): int {
  ensures((r: int) => r >= 0);
  return xs.filter((x) => x === k).length;
}

const TAGS: readonly string[] = ["a", "b", "c"];

export function Tags() {
  const [sel, setSel] = useState<readonly string[]>([]);
  const [ids, setIds] = useState<readonly int[]>([]);
  invariant(distinct(sel) && distinct(ids));
  return (
    <ul>
      {TAGS.map((t) => (
        <li key={t}>
          <button onClick={() => setSel(toggleIn(sel, t))}>{t}</button>
          <span>{countIn(sel, t)}</span>
        </li>
      ))}
      <button onClick={() => setIds(toggleIn(ids, sel.length))}>{ids.length}</button>
    </ul>
  );
}
