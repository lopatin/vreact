// expect: verified
// An int left operand with a number right operand (finding numbers-r1-2): JS widens the int
// (`3 < 5 / 2` is false, `3 * 0.5` is 1.5). The right operand (and the second branch of `?:`) was
// read at the left one's type int and rejected ("type mismatch: expected int, got number"), only
// in this order: `xs.length / 2 > i` was accepted. Now the int is widened (`Num.ofInt i`).
import { requires, ensures, type int } from "vreact/spec";

export function firstHalf(i: int, xs: readonly int[]): boolean {
  return i < xs.length / 2;
}
export function mirror(i: int, xs: readonly int[]): boolean {
  return xs.length / 2 > i;
}
export function atMost(i: int, y: number): boolean {
  return i <= y && i >= y - 1;
}
export function pre(i: int, y: number): number {
  requires(i < y);
  return y;
}
// the caller's `0 < y` and the callee's `i < y` at i = 0 are one term (`Num.ofInt 0 < y`)
export function callPre(y: number): number {
  requires(0 < y);
  return pre(0, y);
}
export function times(i: int, y: number): number {
  const t = i * y;
  return t;
}
export function minusHalf(i: int): number {
  const t = i - 0.5;
  return t;
}
export function plus(i: int, y: number): number {
  const t = i + y;
  return t;
}
export function pick(c: boolean, i: int, y: number): number {
  const t = c ? i : y;
  return t;
}
export function pickLit(c: boolean, i: int): number {
  const t = c ? i : 2.5;
  return t;
}
// branches typed in their narrowed environments
export type U = { readonly kind: "a"; readonly i: int } | { readonly kind: "b"; readonly x: number };
export function val(u: U): number {
  const t = u.kind === "a" ? u.i : u.x;
  return t;
}
export function valNeg(u: U): number {
  const t = u.kind !== "a" ? u.x : u.i;
  return t;
}
// an int with an int stays exact integer arithmetic
export function intStill(i: int): int {
  ensures((r: int) => r === i * 2 + 1);
  const t = i * 2 + 1;
  return t;
}
export function pickInt(c: boolean, i: int): int {
  ensures((r: int) => r === i || r === 3);
  const t = c ? i : 3;
  return t;
}
