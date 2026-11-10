// expect: fail index verdict=not-verified g=incomplete h=incomplete ok=verified proved=1 failed=2 unchecked=2 errors=none
// The index obligations of XS[7] (in g's ensures, in h's requires) fail and are admitted with
// `sorry`, a proof of the false 7 < 2. g's ensures is false (in JS, XS[7] is undefined), and
// so is h's (r = x); the automation proves both through that admitted proof, which its goal
// contains. Such a proof proves nothing: they are blocked (not checked), never proved
// (before: both counted as proved, `vreact:ok`).
import { ensures, requires, type int } from "vreact/spec";
const XS: readonly int[] = [1, 2];
export function g(x: int): int {
  ensures((r: int) => XS[7] === r);
  return x;
}
export function h(x: int): int {
  requires(XS[7] === x);
  ensures((r: int) => r > x);
  return x;
}
export function ok(x: int): int {
  ensures((r: int) => r === x);
  return x;
}
