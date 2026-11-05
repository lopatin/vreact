// expect: fail postcondition verdict=not-verified total=verified prepend=incomplete twice=verified only=verified proved=2 failed=1 unchecked=0 errors=none why.prepend=obligation~of~it~failed
// The remaining limit of proofs/<Mod>.lean for its own module: prepend's ensures needs the
// lemmas, but twice (in this module) calls prepend, so prepend's ensures theorem stays in
// Defs.lean, before the lemmas (twice's obligations may use it): it fails (the documented
// workaround is to move prepend, or twice, to a module that imports this one). The ensures of
// twice and only, which need the same lemmas and which nothing else calls, are proved after
// them in Posts.lean (twice unfolds prepend: its proof does not need prepend's contract).
import { ensures, type int } from "vreact/spec";
export type Line = { readonly id: int; readonly cents: int };
/** @opaque */
export function total(xs: readonly Line[]): int {
  return xs.reduce((acc, l) => acc + l.cents, 0);
}
export function prepend(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + l.cents);
  return [l, ...xs];
}
export function twice(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + 2 * l.cents);
  return prepend(prepend(xs, l), l);
}
export function only(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + l.cents);
  return [l, ...xs];
}
