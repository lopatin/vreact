// expect: verified verdict=verified twice=verified isPlain=verified getB=verified width=verified errors=none
// Property names and string-literal type members whose text looks like an obligation marker,
// or holds `»` or a line break: the generated Lean writes them as «quoted» names with `⟦`, `»`,
// `\` and control characters escaped, so no such name is taken for a copy of obligation 1 (a
// copy without Lean's `vreact:ok` kept twice from counting as proved), and a `»` no longer
// ends the quoted name early (before: Lean parse errors).
import { ensures, type int } from "vreact/spec";
export type Mode = "plain" | "/-⟦ob1⟧-/" | "a»b" | "a\nb" | "a\\u000ab";
export type Rec = { readonly "/-⟦ob1⟧-/": int; readonly "x»y": int; readonly b: int };
export type Shape = { readonly kind: "/-⟦ob1⟧-/"; readonly w: int } | { readonly kind: "dot" };
export function twice(x: int): int {
  ensures((r: int) => r === x + x);
  return 2 * x;
}
export function isPlain(m: Mode): boolean {
  return m === "plain" || m === "a»b";
}
export function getB(r: Rec): int {
  return r.b;
}
export function width(s: Shape): int {
  return s.kind === "dot" ? 0 : s.w;
}
