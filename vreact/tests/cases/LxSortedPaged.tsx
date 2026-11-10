// expect: verified
/// <reference lib="es2023.array" />
// N14/#61: a sortable, paginated table keyed by id: the keys of one sorted page are distinct
// because each list operation is a sub-permutation of its input.
import { useState } from "react";
import { invariant, requires, distinct, type int } from "vreact/spec";

type Item = { readonly id: int; readonly name: string; readonly qty: int };

export function SortedPaged() {
  const [items, setItems] = useState<readonly Item[]>([]);
  const [page, setPage] = useState<int>(0);
  invariant(distinct(items, (x) => x.id));
  const shown = items.toSorted((p, q) => p.qty - q.qty).slice(page * 10, page * 10 + 10);
  return (
    <div>
      <ul>{shown.map((x) => <li key={x.id}>{x.name}</li>)}</ul>
      <button onClick={() => setPage(page + 1)}>next</button>
    </div>
  );
}

type P = { readonly rows: readonly Item[] };

export function Tail(props: P) {
  requires(distinct(props.rows, (r) => r.id));
  return <ul>{props.rows.filter((r) => r.qty > 3).slice(2).toReversed().map((r) => <li key={r.id}>{r.name}</li>)}</ul>;
}
