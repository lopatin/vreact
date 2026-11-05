// expect: reject Lean name clash: the module src/a/b.ts has the Lean namespace VTS.a.b, which src/a.ts already uses for its declaration `b` (Lean and vreact derive names such as VTS.a.b.eq_1 from it
// Lean names the equation lemmas of the definition VTS.a.b (src/a.ts's b) VTS.a.b.eq_1, …: the
// module src/a/b.ts may not declare eq_1 (nor post, post2, …: vreact looks up b's contracts
// by those names).
import { type int } from "vreact/spec";
export function b(x: int): int {
  return x;
}
