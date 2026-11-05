import { requires, ensures, hole, type int } from "vreact/spec";
// (this file starts with a UTF-8 byte-order mark: fills must land at the right offsets)

export type Sel = { readonly items: int; readonly selected?: int };
export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };

export function widthOf(s: Shape): int {
  requires(true); // (not a helper for synth)
  switch (s.kind) {
    case "circle":
      return 0;
    case "rect":
      return s.w;
  }
}

// the fill needs parentheses: (base + 1) * qty
export function total(base: int, qty: int): int {
  requires(qty >= 0);
  ensures((r: int) => r === (base + 1) * qty);
  return hole<int>() * qty;
}

// the fill needs parentheses: -(x + 1)
export function negSucc(x: int): int {
  ensures((r: int) => r === 0 - x - 1);
  return -hole<int>();
}

// not exported
function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}

// two inline object-typed parameters
export function addX(a: { readonly x: int }, b: { readonly y: int; readonly z: int }): int {
  ensures((r: int) => r === a.x + b.y);
  return hole<int>();
}

// optional field: clearing it means `undefined`, not `null`
export function clearSel(s: Sel): Sel {
  ensures((r: Sel) => r.selected === undefined && r.items === s.items);
  return hole<Sel>();
}

// narrowing by early return: x is not null at the hole
export function succ(x: int | null): int {
  ensures((r: int) => x === null || r === x + 1);
  if (x === null) return 0;
  return hole<int>();
}

// narrowing by early return: s is a rect at the hole
export function width(s: Shape): int {
  ensures((r: int) => r === widthOf(s));
  if (s.kind !== "rect") return 0;
  return hole<int>();
}

// a precondition outside the default random range
export function bonus(points: int): int {
  requires(points >= 100);
  ensures((r: int) => r >= 100);
  return hole<int>();
}

// no input satisfies the precondition: candidates go to Lean untested (vacuously proved)
export function never(x: int): int {
  requires(x > x);
  ensures((r: int) => r > x);
  return hole<int>();
}
