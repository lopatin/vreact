// expect: reject === on values of the type parameter T is not supported: T has no equality constraint
// === on an unconstrained type parameter: JS compares objects by identity (and numbers by IEEE
// rules), Lean's = structurally; an equality constraint restricts T to types compared by value.
import { ensures, requires, type int } from "vreact/spec";

export function same<T>(x: T, y: T): boolean {
  return x === y;
}
