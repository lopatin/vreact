// expect: verified
import { ensures, requires, type int } from "vreact/spec";

// [...m], [...m.values()] have m.size elements
export type MxslItem = { readonly id: int; readonly qty: int };

export function mxslFirstVal(m: ReadonlyMap<string, int>): int {
  requires(m.size > 0);
  const [, v] = [...m][0];
  return v;
}

export function mxslFirstItem(m: ReadonlyMap<int, MxslItem>): MxslItem {
  requires(m.size > 0);
  return [...m.values()][0];
}

export function mxslValues(m: ReadonlyMap<int, MxslItem>): readonly MxslItem[] {
  ensures((r: readonly MxslItem[]) => r.length === m.size);
  return [...m.values()];
}

export function mxslEntries(m: ReadonlyMap<int, MxslItem>): readonly [int, MxslItem][] {
  ensures((r: readonly [int, MxslItem][]) => r.length === m.size);
  return [...m];
}
