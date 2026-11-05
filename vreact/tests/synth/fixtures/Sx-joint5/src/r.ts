import { ensures, hole, type int } from "vreact/spec";

export type Action = { readonly kind: "a" } | { readonly kind: "b" } | { readonly kind: "c" } | { readonly kind: "d" } | { readonly kind: "e" };
export type Counter = { readonly total: int; readonly ops: int };

// one hole per case: a call reaches exactly one of them, so each hole is searched once, whatever
// the others are filled with. Cases a–d are easy; case e has no straight-line solution (no
// multiplication), and since its search does not depend on the other fills, no other fill of
// holes 1–4 is tried (before: 3^4 = 81 searches of hole 5)
export function step(s: Counter, a: Action): Counter {
  ensures((r: Counter) => r.ops === s.ops + 1);
  ensures((r: Counter) => a.kind !== "e" || r.total === s.total * s.total);
  switch (a.kind) {
    case "a":
      return hole<Counter>();
    case "b":
      return hole<Counter>();
    case "c":
      return hole<Counter>();
    case "d":
      return hole<Counter>();
    case "e":
      return hole<Counter>();
  }
}

// the same shape, all cases solvable: proved together, each hole searched once
export function step5(s: Counter, a: Action): Counter {
  ensures((r: Counter) => r.ops === s.ops + 1 && r.total === (a.kind === "e" ? 0 : s.total));
  switch (a.kind) {
    case "a":
      return hole<Counter>();
    case "b":
      return hole<Counter>();
    case "c":
      return hole<Counter>();
    case "d":
      return hole<Counter>();
    case "e":
      return hole<Counter>();
  }
}

// both holes are evaluated in one call: the search of hole 2 depends on the fill of hole 1
// (hole 1 cannot be tested alone: every call reaches hole 2)
export function twice(x: int): int {
  ensures((r: int) => r === x + 2);
  const y: int = hole<int>();
  return y + hole<int>();
}
