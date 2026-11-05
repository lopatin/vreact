// expect: reject Lean name clash: the module src/a/b.ts has the Lean namespace VTS.a.b, which src/a.ts already uses for its declaration `b`
// src/a.ts declares b (VTS.a.b, and VTS.a.b.post for its ensures); src/a/b.ts is the module
// VTS.a.b and declares post (VTS.a.b.post again): no Lean module can import both (before: a
// Lean build error "environment already contains 'VTS.a.b.post'" and c's function UNCHECKED).
import { ensures, type int } from "vreact/spec";
/** @opaque */
export function b(x: int): int {
  ensures((r: int) => r > x);
  return x + 1;
}
