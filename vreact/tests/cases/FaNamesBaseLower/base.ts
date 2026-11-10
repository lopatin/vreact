// expect: verified verdict=verified inca=verified twice=verified thrice=verified errors=none
// src/base.ts is VTS.base_ (on a case-insensitive disk proofs/base.lean is proofs/Base.lean, the
// global lemma file): its lemmas are proofs/base_.lean, next to the global proofs/Base.lean.
import { ensures, type int } from "vreact/spec";
/** @opaque */
export function inca(x: int): int {
  return x + 1;
}
export function twice(x: int): int {
  ensures((r: int) => r > x);
  return inca(inca(x));
}
