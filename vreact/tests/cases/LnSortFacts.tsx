// expect: verified
/// <reference lib="es2023.array" />
// toSorted is a permutation (length, membership, distinct keys), slice a sublist,
// range(n) distinct, toReversed a reversal — whatever the comparator.
import { useState } from "react";
import { requires, ensures, invariant, distinct, implies, range, type int } from "vreact/spec";

type Row = { readonly id: int; readonly age: int };

export function smallest(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r: int) => xs.includes(r));
  const s = xs.toSorted((a: int, b: int) => a - b);
  return s[0];
}

export function sortByAge(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (x) => x.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id) && r.length === xs.length);
  return xs.toSorted((p, q) => (p.age < q.age ? -1 : 1));
}

export function firstN(xs: readonly Row[], n: int): readonly Row[] {
  requires(distinct(xs, (x) => x.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.slice(0, n);
}

export function push(past: readonly int[], v: int): readonly int[] {
  ensures((r: readonly int[]) => implies(past.every((x) => x >= 0) && v >= 0, r.every((x) => x >= 0)));
  return past.length >= 20 ? [...past.slice(1), v] : [...past, v];
}

export function LnTable() {
  const [rows] = useState<readonly Row[]>([]);
  const [page, setPage] = useState<int>(0);
  invariant(distinct(rows, (r) => r.id));
  const sorted = rows.toSorted((a, b) => a.age - b.age);
  const shown = rows.slice(page * 10, page * 10 + 10);
  return (
    <div>
      <ul>{sorted.map((r) => <li key={r.id}>{r.age}</li>)}</ul>
      <ul>{shown.map((r) => <li key={r.id}>{r.age}</li>)}</ul>
      <ul>{rows.toReversed().map((r) => <li key={r.id}>{r.age}</li>)}</ul>
      <div>{range(5).map((i) => <span key={i}>★</span>)}</div>
      <button onClick={() => setPage(page + 1)}>next</button>
    </div>
  );
}
