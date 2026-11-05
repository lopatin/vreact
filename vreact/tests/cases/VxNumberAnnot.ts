// expect: verified
// `number` annotates an int-valued parameter exactly (`int` is TypeScript's `number`): the map
// index and a forall variable (formerly rejected: "annotated number but receives int").
import { ensures, requires, forall, type int } from "vreact/spec";
export function f(xs: readonly int[]): readonly int[] {
  ensures((r: readonly int[]) => r.length === xs.length);
  return xs.map((x: int, i: number) => x + i);
}
export function g(xs: readonly int[]): int {
  requires(forall(0, xs.length, (i: number) => xs[i] >= 0));
  ensures((r: number) => r === xs.length && forall(0, r, (j: number) => xs[j] >= 0));
  return xs.length;
}
