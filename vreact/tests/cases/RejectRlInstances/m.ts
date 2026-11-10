// expect: reject proofs/m.lean:6:1: `instance (priority := high) allEq : BEq Int ;; an instance can change the meaning of the generated code ;; proofs/m.lean:7:1: `instance (priority := high) : DecidableEq VTS.m.Hold ;; proofs/m.lean:8:1: `instance (priority := high) : JS.ToJS Int ;; proofs/m.lean:9:1: `deriving instance BEq for VTS.m.Hold` ;; proofs/m.lean:10:3: the attribute `instance` ;; proofs/m.lean:11:12: the attribute `instance` ;; proofs/m.lean:12:12: `-instance` ;; proofs/m.lean:13:3: the attribute `implemented_by allEq'` ;; proofs/m.lean:14:3: the attribute `reducible` ;; proofs/m.lean:15:3: `scoped simp`: scoped attributes ;; proofs/m.lean:16:3: the attribute `extern
// Instances and attributes in a user proof that change the meaning of the generated code
// (R4 item 12). Before the whitelist, proofs/m.lean's `allEq` (imported by use.ts's Defs) made
// `[inc(0)].includes(x)` true for every x in Lean, so hasOne's false ensures was VERIFIED with
// no axiom. Instances (also derived, or by attribute), erasing an instance, and every attribute
// other than simp/vreact_simp/grind (implemented_by, extern, reducible, scoped …) are rejected.
import { ensures, type int } from "vreact/spec";
export type Hold = { readonly id: int; readonly price: int };
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
export function same(a: Hold, b: Hold): boolean {
  return a.id === b.id && a.price === b.price;
}
