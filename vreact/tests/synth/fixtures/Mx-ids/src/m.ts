import { ensures, hole, type int } from "vreact/spec";

// random inputs are values of the parameter's type: a record's `id` is set to the Map key (or to a
// distinct int in an array) only when the id has that type
type Color = "red";
type Tag = { readonly id: Color; readonly w: int };
type Named = { readonly id: string; readonly w: int };

export function allRed(m: ReadonlyMap<string, Tag>): boolean {
  ensures((r) => r === [...m.values()].every((t) => t.id === "red"));
  return hole<boolean>();
}

export function allNamed(xs: readonly Named[]): boolean {
  ensures((r) => r === xs.every((t) => t.id.length >= 0));
  return hole<boolean>();
}

// [...m.values()].length is m.size (Lean knows it)
export function nValues(m: ReadonlyMap<boolean, readonly int[]>): int {
  ensures((r) => r === [...m.values()].length);
  return hole<int>();
}
