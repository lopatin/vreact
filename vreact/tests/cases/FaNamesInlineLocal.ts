// expect: verified f=verified g=verified
// A local's inline record type is named after the local (`point` → `Point`), which is a
// constant of the module; a local's inline union, after a function of the module (`Shape`); two
// locals' different inline unions share their hint (`S`): every type gets its own name.
import { ensures, type int } from "vreact/spec";

export const Point: int = 3;

export function Shape(x: int): int {
  return x;
}

export function f(): int {
  ensures((r) => r === 3);
  const point: { readonly x: int } = { x: Point };
  const shape: { readonly kind: "a"; readonly n: int } | { readonly kind: "b" } = { kind: "a", n: Shape(point.x) };
  return shape.kind === "a" ? shape.n : 0;
}

export function g(): int {
  ensures((r) => r === 1);
  const s: { readonly kind: "a" } | { readonly kind: "b"; readonly m: int } = { kind: "b", m: 1 };
  return s.kind === "b" ? s.m : 0;
}

export function h(): int {
  ensures((r) => r === 2);
  const s: { readonly kind: "c"; readonly k: int } | { readonly kind: "d" } = { kind: "c", k: 2 };
  return s.kind === "c" ? s.k : 0;
}
