// expect: reject compares object identity in JS (a copy is never found)
// [p].includes({ ...p }) is false in JS (SameValueZero is reference identity on objects).
import { type int } from "vreact/spec";

type P = { readonly x: int; readonly y: int };

export function containsCopy(p: P): boolean {
  return [p].includes({ x: p.x, y: p.y });
}
