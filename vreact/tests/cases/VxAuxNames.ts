// expect: verified
// Names Lean reserves or reads specially: a constructor `rec_1` (an auxiliary-recursor name)
// crashed Lean 4.35, and `_`-names (`_hyg` marks hygienic names, `_cstage1`, `_spec_1`,
// `_elambda` are compiler auxiliaries) crashed or broke it as constructors, fields, functions,
// constants and locals.
import { ensures, implies, type int } from "vreact/spec";
type K = "rec_1" | "below" | "brecOn_1" | "_cstage1" | "_hyg" | "_spec_1" | "_elambda" | "_" | "_x" | "a";
type P = { readonly _cstage1: int; readonly _hyg: int; readonly rec_1: int; readonly _: int };
type U = { readonly kind: "rec_1"; readonly x: int } | { readonly kind: "_hyg"; readonly x: int; readonly _spec_1: int };
export const _elambda_1: int = 3;
export function _cstage1(_hyg: int): int {
  const _spec_1 = _hyg + 1;
  return _spec_1;
}
export function f(p: P, k: K, u: U): int {
  ensures((r: int) => implies(k === "rec_1" && u.kind === "rec_1", r === p._cstage1 + p._hyg + p.rec_1 + p._ + 1 + u.x + 4));
  return p._cstage1 + p._hyg + p.rec_1 + p._ + (k === "rec_1" ? 1 : 0) + u.x + _cstage1(_elambda_1);
}
export function g(k: K): string {
  ensures((r: string) => implies(k === "_hyg", r === "_hyg") && implies(k === "rec_1", r === "rec_1"));
  return k;
}
export function h(u: U): int {
  ensures((r: int) => implies(u.kind === "_hyg", r === u.x + 1));
  switch (u.kind) {
    case "rec_1":
      return 0;
    case "_hyg":
      return u.x + 1;
  }
}
