// expect: fail index
// The body of a parenthesized quantifier arrow is still checked: `r[0]` without a guard may be
// out of bounds.
import { requires, type int } from "vreact/spec";

export function firstOk(xss: readonly (readonly int[])[]): boolean {
  requires(xss.every(((r) => r[0] > 0)));
  return xss.length > 0;
}
