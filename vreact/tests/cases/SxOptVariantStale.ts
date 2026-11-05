// expect: fail postcondition
// Reassigning a `let` ends its variant narrowing too: after `s = q`, s is q (null when q is),
// so r === area(p) is false in JS for q = null and a rect p of width 3.
import { ensures, type int } from "vreact/spec";

export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };

export function area(s: Shape): int {
  switch (s.kind) {
    case "circle":
      return 0;
    case "rect":
      return s.w;
  }
}

export function stale(p: Shape | null, q: Shape | null): int {
  ensures((r: int) => p === null || (p.kind === "circle" || r === area(p)));
  let s: Shape | null = p;
  if (s === null) return 0;
  if (s.kind === "circle") return 0;
  s = q;
  return s === null ? 0 : area(s);
}
