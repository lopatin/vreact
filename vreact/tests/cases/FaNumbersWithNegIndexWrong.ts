// expect: fail index postcondition tooFar=incomplete wrongEnd=incomplete
/// <reference lib="es2023.array" />
// A negative `with` index counts from the end (numbers-r1-3): -2 on a one-element array is a
// RangeError, and -1 writes the last element, not the first.
import { ensures, requires, type int } from "vreact/spec";

export function tooFar(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  return xs.with(-2, v);
}
export function wrongEnd(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 1);
  ensures((r: readonly int[]) => r[0] === v);
  return xs.with(-1, v);
}
