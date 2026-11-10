import { ensures, hole, type int } from "vreact/spec";

export type Sel = { readonly items: int; readonly selected?: int };

// exactOptionalPropertyTypes (tsconfig): `selected: undefined` passes the tests but does not
// typecheck, so no candidate reaches Lean — not "Lean rejects"
export function clearSel(s: Sel): Sel {
  ensures((r: Sel) => r.selected === undefined && r.items === s.items);
  return hole<Sel>();
}

// no solution in the grammar (no multiplication): stays a hole
export function sq(x: int): int {
  ensures((r: int) => r === x * x);
  return hole<int>();
}

// the contract calls the unfinished sq: not "postcondition fails", and not searched
export function plusSq(x: int): int {
  ensures((r: int) => r === sq(x) + 1);
  return hole<int>();
}

/** @trusted */
export function stubSq(x: int): int {
  ensures((r: int) => r >= 0);
  return hole<int>();
}

// the contract calls a trusted stub whose body is a hole: the tests cannot evaluate it (Lean can)
export function viaStub(x: int): int {
  ensures((r: int) => r === stubSq(x) + 1);
  return hole<int>();
}
