// expect: verified Labels=verified
// V4: distinct keys through a map that keeps the key, followed by slice/filter
// (`xs.map(bump).slice(0, 3)`); the reversed order already verified.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Row = { readonly id: int; readonly age: int; readonly name: string };
function bump(r: Row): Row { return { ...r, age: r.age + 1 }; }
export function mapThenSlice(xs: readonly Row[]): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.map((r) => bump(r)).slice(0, 3);
}
export function mapFilterSlice(xs: readonly Row[], k: int): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  return xs.filter((r) => r.age > k).map((r) => bump(r)).filter((r) => r.age < 90).slice(1, 4);
}
export function inlineUpdate(xs: readonly Row[], id: int): readonly Row[] {
  requires(distinct(xs, (r) => r.id));
  ensures((r: readonly Row[]) => distinct(r, (x) => x.id));
  const ys: readonly Row[] = xs.map((r) => (r.id === id ? { ...r, name: "x" } : r));
  return ys.slice(0, 2);
}
function upper(r: Row): Row { return { ...r, name: r.name.toUpperCase() }; }
export function Labels(props: { rows: readonly Row[] }) {
  requires(distinct(props.rows, (r) => r.id));
  return <ul>{props.rows.map((r) => upper(r)).slice(0, 3).map((r) => <li key={r.id}>{r.name}</li>)}</ul>;
}
