// expect: reject Math.max on a value of the type parameter K is not supported: its values are abstract
// TypeScript accepts Math.* on K extends int (a subtype of number); in Lean K is abstract (this
// reached Lean ill-typed before: an internal error).
import { type int } from "vreact/spec";

export function larger<K extends int>(a: K, b: K): int {
  return Math.max(a, b);
}
