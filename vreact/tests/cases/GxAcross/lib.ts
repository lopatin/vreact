import { ensures, distinct, type int } from "vreact/spec";

export type Todo = { readonly id: int; readonly title: string; readonly done: boolean };

/** @opaque */
export function upsertById<T extends { readonly id: int }>(xs: readonly T[], x: T): readonly T[] {
  ensures((r: readonly T[]) => r.some((y) => y.id === x.id));
  ensures((r: readonly T[]) => !distinct(xs, (y) => y.id) || distinct(r, (y) => y.id));
  if (xs.some((y) => y.id === x.id)) return xs.map((y) => (y.id === x.id ? x : y));
  return [...xs, x];
}

/** @opaque */
export function removeById<T extends { readonly id: int }>(xs: readonly T[], id: int): readonly T[] {
  ensures((r: readonly T[]) => !r.some((y) => y.id === id));
  ensures((r: readonly T[]) => !distinct(xs, (y) => y.id) || distinct(r, (y) => y.id));
  return xs.filter((y) => y.id !== id);
}
