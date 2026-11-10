// expect: status pending=incomplete done=verified
// hole<T>() in a generic body (a synthesis placeholder of a type mentioning the type parameter):
// `(sorry : List T)`, its contracts pending (INCOMPLETE), the rest of the module checked.
import { ensures, hole, type int } from "vreact/spec";

export function pending<T extends { readonly id: int }>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.length === xs.length + 1);
  const ys: readonly T[] = hole<readonly T[]>();
  return [...ys, x];
}

export function done<T extends { readonly id: int }>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.length === xs.length + 1 && r.some((y) => y.id === x.id));
  return [...xs, x];
}
