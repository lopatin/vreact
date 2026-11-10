// expect: verified
/// <reference lib="es2023.array" />
// `xs.with(-1, v)` writes the last element: JS reads a negative index from the end and throws a
// RangeError only outside [-length, length) (finding numbers-r1-3; the obligation was 0 ≤ -1).
// An index written `-k` is `withEnd xs k` (obligation 0 < k ≤ length); `-0` is index 0.
import { ensures, requires, type int } from "vreact/spec";

export function setLast(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  ensures((r: readonly int[]) => r.length === xs.length && r[xs.length - 1] === v);
  return xs.with(-1, v);
}
export function setFromEnd(xs: readonly int[], k: int, v: int): readonly int[] {
  requires(0 < k && k <= xs.length);
  ensures((r: readonly int[]) => r.length === xs.length && r[xs.length - k] === v);
  return xs.with(-k, v);
}
export function setFirst(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  ensures((r: readonly int[]) => r.length === xs.length && r[0] === v);
  return xs.with(-xs.length, v);
}
export function negZero(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  ensures((r: readonly int[]) => r.length === xs.length && r[0] === v);
  return xs.with(-0, v);
}
