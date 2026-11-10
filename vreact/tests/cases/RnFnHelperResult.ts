// expect: reject the result of mk has the function type (y: int) => int, which is not data
// A local helper's result annotation is the type of the value it is inlined to: an array of
// functions has no Lean value type (formerly an internal error, "function type has no Lean value
// type").
import { type int } from "vreact/spec";

export function f(x: int): int {
  const mk = (): readonly ((y: int) => int)[] => [];
  return mk().length + x;
}
