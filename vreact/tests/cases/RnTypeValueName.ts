// expect: reject `Limits` names both a type (line 7) and a constant of this module
// TypeScript keeps types and values apart (the "companion" pattern), but both would be the Lean
// declaration VTS.RnTypeValueName.Limits (formerly an internal error in the generated Lean,
// "has already been declared").
import { type int, ensures } from "vreact/spec";

type Limits = { readonly max: int };
function mk(n: int): Limits {
  const r: Limits = { max: n };
  return r;
}
export const Limits: Limits = mk(3);
export function top(): int {
  ensures((r) => r === 3);
  return Limits.max;
}
