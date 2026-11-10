// expect: verified
// A parenthesized arrow, `xs.every(((r) => c))` or `forall(lo, hi, ((i) => c))`, is the quantifier
// as without the parentheses: read as a contract, the consequent of implies(a, b) under its guard
// (the code reading would evaluate `r[0]` / `xss[i][0]` unguarded and fail an index obligation).
import { requires, forall, exists, implies, type int } from "vreact/spec";

export function firstOk(xss: readonly (readonly int[])[]): boolean {
  requires(xss.every(((r) => implies(r.length > 0, r[0] > 0))));
  requires(forall(0, xss.length, ((i) => implies(xss[i].length > 0, xss[i][0] > 0))));
  requires(xss.some(((r) => implies(r.length > 0, r[0] > 0))) || exists(0, xss.length, ((i) => implies(xss[i].length > 0, xss[i][0] > 0))) || xss.length === 0);
  return xss.length > 0;
}
