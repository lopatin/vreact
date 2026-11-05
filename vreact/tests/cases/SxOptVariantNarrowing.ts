// expect: verified
// A path of type `T | null` tested non-null and then to be a variant is that present variant:
// as a whole value (a call, a return, a later null test or truthiness test), and through
// several exclusions on a union of three variants (the remaining arm is split per variant).
import { ensures, type int } from "vreact/spec";

export type T = { readonly kind: "a"; readonly x: int } | { readonly kind: "b"; readonly y: int } | { readonly kind: "c"; readonly y: int; readonly z: int };
export type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "rect"; readonly w: int; readonly h: int };
export type Box = { readonly inner: T | null; readonly n: int };

export function area(s: Shape): int {
  switch (s.kind) {
    case "circle":
      return 0;
    case "rect":
      return s.w;
  }
}

export function zOpt(t: T | null): int {
  ensures((r: int) => t === null || (t.kind !== "c" || r === t.z));
  if (t === null) return 0;
  if (t.kind === "a") return 0;
  if (t.kind === "b") return 1;
  return t.z;
}

export function zBox(b: Box): int {
  ensures((r: int) => b.inner === null || (b.inner.kind !== "c" || r === b.inner.z));
  if (b.inner === null) return 0;
  if (b.inner.kind === "a") return 0;
  if (b.inner.kind === "b") return 1;
  return b.inner.z;
}

export function areaOpt(s: Shape | null): int {
  ensures((r: int) => s === null || (s.kind === "circle" || r === area(s)));
  if (s === null) return 0;
  if (s.kind === "circle") return 0;
  return area(s);
}

export function present(s: Shape | null): int {
  ensures((r: int) => s === null || (s.kind === "circle" || r === s.w));
  if (s === null) return 0;
  if (s.kind === "circle") return 0;
  if (s !== null) return s.w;
  return 5;
}

export function truthy(s: Shape | null): int {
  ensures((r: int) => s === null || (s.kind === "circle" || r === s.h));
  if (!s) return 0;
  if (s.kind === "circle") return 0;
  if (s) return s.h;
  return 5;
}

export function keep(s: Shape | null): Shape | null {
  ensures((r: Shape | null) => (r === null) === (s === null));
  if (s === null) return s;
  if (s.kind === "circle") return s;
  return s;
}
