// expect: verified cap=verified Config=verified
// An inline record type is named after its constant (`Config`), which is also the constant's Lean
// name VTS.<module>.Config: the type gets a fresh name (Config₂) instead of a Lean "already
// declared" error.
import { ensures, type int } from "vreact/spec";

export const Config: { readonly max: int } = { max: 3 };

export function cap(x: int): int {
  ensures((r) => r <= Config.max);
  return x > Config.max ? Config.max : x;
}
