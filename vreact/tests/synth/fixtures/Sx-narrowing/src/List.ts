import { requires, ensures, hole, type int } from "vreact/spec";
// (the module of List.ts is VTS.List_: synth names its types as the translator does)
// The scope at each hole has the narrowing the translator has there, the complement of a test
// included (early return, else branch, ternary, `||`): s.w / s.h are in scope.

export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };
export type Tri = { readonly kind: "a"; readonly x: int } | { readonly kind: "b"; readonly x: int; readonly y: int } | { readonly kind: "c"; readonly y: int };

export function widthOf(s: Shape): int {
  requires(true); // (not a helper for synth)
  switch (s.kind) {
    case "circle":
      return 0;
    case "rect":
      return s.w;
  }
}

// early return on the other variant: s is a rect at the hole
export function width2(s: Shape): int {
  ensures((r: int) => r === widthOf(s));
  if (s.kind === "circle") return 0;
  return hole<int>();
}

// else branch
export function w4(s: Shape): int {
  ensures((r: int) => s.kind === "circle" || r === widthOf(s) + 1);
  if (s.kind === "circle") {
    return 0;
  } else {
    return hole<int>();
  }
}

// ternary
export function w6(s: Shape): int {
  ensures((r: int) => s.kind === "circle" || r === s.w + s.h);
  return s.kind === "circle" ? 0 : hole<int>();
}

// `||` with an early return
export function w7(s: Shape, k: int): int {
  ensures((r: int) => s.kind === "circle" || r === (k < 0 ? 0 : s.h + k));
  if (s.kind === "circle" || k < 0) return 0;
  return hole<int>();
}

// two variants remain: no fields beyond the shared ones
export function triX(t: Tri): int {
  ensures((r: int) => r === 0 || t.kind === "a");
  if (t.kind === "a") return 1;
  return hole<int>();
}
