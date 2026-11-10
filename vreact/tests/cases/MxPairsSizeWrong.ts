// expect: fail postcondition
import { ensures, type int } from "vreact/spec";

// wrong: without distinct ids, new Map(pairs) keeps one entry per id (and new Set(xs) one per value)
export type MxpsItem = { readonly id: int; readonly name: string };

export function mxpsMapSize(xs: readonly MxpsItem[]): int {
  ensures((r) => r === xs.length);
  return new Map<int, MxpsItem>(xs.map((x: MxpsItem) => [x.id, x])).size;
}

export function mxpsSetSize(xs: readonly int[]): int {
  ensures((r) => r === xs.length);
  return new Set(xs).size;
}
