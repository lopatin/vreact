// expect: verified
// N15 (b7 "delete current"): deleting the selected element by id keeps the list non-empty when it
// had two or more elements, because the ids are distinct (exactly one element is removed). The
// handler's outcome indexes `items[sel]` with a proof from the invariant, so the invariant is
// exposed although the goal depends on it; the filter predicate with an index obligation is
// translated over `items.attach` and returns to `items` once the obligation is proved.
import { useState } from "react";
import { invariant, requires, ensures, distinct, type int } from "vreact/spec";

type Item = { readonly id: int; readonly name: string };

// the index inside the filter predicate
export function D() {
  const [items, setItems] = useState<readonly Item[]>([{ id: 0, name: "a" }]);
  const [sel, setSel] = useState<int>(0);
  invariant(items.length > 0 && 0 <= sel && sel < items.length && distinct(items, (i) => i.id));
  return (
    <button
      onClick={() => {
        if (items.length <= 1) return;
        setItems(items.filter((i) => i.id !== items[sel].id));
        setSel(0);
      }}
    >
      del
    </button>
  );
}

// the selected id bound before the filter
export function D2() {
  const [items, setItems] = useState<readonly Item[]>([{ id: 0, name: "a" }]);
  const [sel, setSel] = useState<int>(0);
  invariant(items.length > 0 && 0 <= sel && sel < items.length && distinct(items, (i) => i.id));
  return (
    <button
      onClick={() => {
        if (items.length <= 1) return;
        const id = items[sel].id;
        setItems(items.filter((i) => i.id !== id));
        setSel(0);
      }}
    >
      del
    </button>
  );
}

// b7 SelIdx: two invariants, a rendered selection and the other handlers
export function SelIdx() {
  const [items, setItems] = useState<readonly Item[]>([{ id: 0, name: "a" }]);
  const [sel, setSel] = useState<int>(0);
  const [nextId, setNextId] = useState<int>(1);
  invariant(items.length > 0 && 0 <= sel && sel < items.length);
  invariant(distinct(items, (i) => i.id) && items.every((i) => i.id < nextId));
  return (
    <div>
      <p>{items[sel].name}</p>
      <button onClick={() => setSel(sel + 1 < items.length ? sel + 1 : 0)}>next</button>
      <button onClick={() => { setItems([...items, { id: nextId, name: "n" }]); setNextId(nextId + 1); }}>add</button>
      <button
        onClick={() => {
          if (items.length <= 1) return;
          const rest = items.filter((i) => i.id !== items[sel].id);
          setItems(rest);
          setSel(rest.length - 1);
        }}
      >
        delete current
      </button>
    </div>
  );
}

// the count of the remaining elements, as a function
export function removeSelected(items: readonly Item[], sel: int): readonly Item[] {
  requires(0 <= sel && sel < items.length && distinct(items, (i) => i.id));
  ensures((r: readonly Item[]) => r.length === items.length - 1);
  return items.filter((i) => i.id !== items[sel].id);
}
