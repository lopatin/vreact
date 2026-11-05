// expect: verified
// An int[] where an (int | null)[] is expected (a spread, an argument, a return value): each element
// is widened, the same JS array.
import { ensures, type int } from "vreact/spec";
export function s(xs: readonly int[]): readonly (int | null)[] {
  ensures((r: readonly (int | null)[]) => r.length === xs.length + 1);
  const ys: readonly (int | null)[] = [...xs, null];
  return ys;
}
export function count(ys: readonly (int | null)[]): int {
  ensures((r: int) => r === ys.length);
  return ys.length;
}
export function t(xs: readonly int[]): int {
  ensures((r: int) => r === xs.length);
  return count(xs);
}
export function u(xs: readonly int[]): readonly (number | undefined)[] {
  ensures((r: readonly (number | undefined)[]) => r.length === xs.length);
  return xs;
}
