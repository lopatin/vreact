import { ensures, hole, type int } from "vreact/spec";

// three variants; "b" and "c" share y
export type T = { readonly kind: "a"; readonly x: int } | { readonly kind: "b"; readonly y: int } | { readonly kind: "c"; readonly y: int; readonly z: int };
export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };
export type Box = { readonly inner: T | null; readonly n: int };
export type SBox = { readonly inner: Shape | null; readonly n: int };

// several exclusions: only "c" is left
export function zOf(t: T): int {
  ensures((r: int) => t.kind !== "c" || r === t.z);
  if (t.kind === "a") return 0;
  if (t.kind === "b") return 1;
  return hole<int>();
}

// one exclusion: "b" or "c", which share y
export function yOf(t: T): int {
  ensures((r: int) => t.kind === "a" || r === t.y + 1);
  if (t.kind === "a") return 0;
  return hole<int>();
}

// both exclusions in one condition
export function zAnd(t: T): int {
  ensures((r: int) => t.kind !== "c" || r === t.z + 1);
  if (t.kind !== "a" && t.kind !== "b") return hole<int>();
  return 0;
}

// a chain of ternaries
export function zTern(t: T): int {
  ensures((r: int) => t.kind !== "c" || r === t.z + t.y);
  return t.kind === "a" ? 0 : t.kind === "b" ? 1 : hole<int>();
}

// optional parameter: null, then two exclusions
export function zOpt(t: T | null): int {
  ensures((r: int) => t === null || (t.kind !== "c" || r === t.z));
  if (t === null) return 0;
  if (t.kind === "a") return 0;
  if (t.kind === "b") return 1;
  return hole<int>();
}

// an optional field: null, then two exclusions
export function zBox(b: Box): int {
  ensures((r: int) => b.inner === null || (b.inner.kind !== "c" || r === b.inner.z));
  if (b.inner === null) return 0;
  if (b.inner.kind === "a") return 0;
  if (b.inner.kind === "b") return 1;
  return hole<int>();
}

// optional parameter, two variants: null, then the other variant (a variant implies present)
export function wOpt(s: Shape | null): int {
  ensures((r: int) => s === null || (s.kind === "circle" || r === s.w));
  if (s === null) return 0;
  if (s.kind === "circle") return 0;
  return hole<int>();
}

// an optional field: null early return, then a switch on the variant
export function wSwitch(b: SBox): int {
  ensures((r: int) => b.inner === null || (b.inner.kind === "circle" || r === b.inner.w));
  if (b.inner === null) return 0;
  switch (b.inner.kind) {
    case "circle":
      return 0;
    case "rect":
      return hole<int>();
  }
}

// an optional field: the null test and the variant test in one condition
export function wAnd(b: SBox): int {
  ensures((r: int) => b.inner === null || (b.inner.kind === "circle" || r === b.inner.h));
  if (b.inner !== null && b.inner.kind === "rect") return hole<int>();
  return 0;
}

// after an if that does not return, both "b" and "c" reach the hole: y only, not z
export function noOver(t: T): int {
  ensures((r: int) => t.kind === "a" || r === t.y);
  if (t.kind === "a") return 0;
  let k = 0;
  if (t.kind === "b") k = 1;
  return hole<int>();
}
