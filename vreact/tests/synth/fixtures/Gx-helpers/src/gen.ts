import { ensures, hole, type int } from "vreact/spec";

export type Color = "red" | "green";

// a generic helper is offered at the hole's types (here K = int): toggleIn(sel, id)
/** @opaque */
export function toggleIn<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.includes(k) === !xs.includes(k));
  return xs.includes(k) ? xs.filter((x) => x !== k) : [...xs, k];
}

export function flip(sel: readonly int[], id: int): readonly int[] {
  ensures((r: readonly int[]) => r.includes(id) === !sel.includes(id));
  return hole<readonly int[]>();
}

// the filter-by-key grammar for a field-constrained element type (no `{ ...x, f }`: not a T)
export function removeById<T extends { readonly id: int }>(xs: readonly T[], id: int): readonly T[] {
  ensures((r: readonly T[]) => !r.some((y) => y.id === id) && r.every((y) => xs.some((z) => z.id === y.id)));
  ensures((r: readonly T[]) => xs.every((z) => z.id === id || r.some((y) => y.id === z.id)));
  return hole<readonly T[]>();
}

// an optional constrained field is absent as undefined (never null) in the test inputs: `0`
// passes only if no input has note: null (null.length throws)
export function zeroNote<T extends { readonly note?: string }>(x: T): int {
  ensures((r: int) => r === 0 && (x.note === undefined || x.note.length >= 0));
  return hole<int>();
}

// an equality constraint by an enum: tested at int and string, which stand for every such type
export function firstKey<K extends Color>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.includes(k));
  return hole<readonly K[]>();
}
