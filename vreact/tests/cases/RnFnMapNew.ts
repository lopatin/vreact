// expect: reject new Map<…> has the function type (x: int) => int, which is not data
// A function type inside the type arguments of `new Map<…>` (in an array value): rejected like
// the same type anywhere else data is needed (it crashed the translator: "function type has no
// Lean value type").
import { ensures, type int } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 0);
  const m = new Map<int, readonly ((x: int) => int)[]>();
  return m.size;
}
