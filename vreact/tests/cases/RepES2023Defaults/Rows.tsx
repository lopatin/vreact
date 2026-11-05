// expect: verified verdict=verified
// No tsconfig.json: vreact's built-in compiler options must include the ES2023 library,
// since toSorted / toReversed / with are part of VTS.
import { requires, distinct, type int } from "vreact/spec";
type Row = { readonly id: int; readonly n: int };
type P = { readonly rows: readonly Row[] };
export function sorted(xs: readonly int[]): readonly int[] {
  return xs.toSorted((a, b) => a - b);
}
export function firstToZero(xs: readonly int[]): readonly int[] {
  requires(xs.length > 0);
  return xs.with(0, 0);
}
export function Rows(props: P) {
  requires(distinct(props.rows, (r) => r.id));
  return <ul>{props.rows.toReversed().map((r) => <li key={r.id}>{r.n}</li>)}</ul>;
}
