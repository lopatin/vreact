// expect: verified
// A parenthesized arrow, `xs.every(((r) => c))` or `forall(lo, hi, ((i) => c))`, is the quantifier
// as without the parentheses: its body is read under the quantifier's guard (each element, or
// lo <= i < hi). (In a requires JS evaluates both arguments of implies(a, b), so the guard of an
// index is written `!a || b`: fa/implies.)
import { requires, forall, exists, type int } from "vreact/spec";

export function firstOk(xss: readonly (readonly int[])[]): boolean {
  requires(xss.every(((r) => r.length === 0 || r[0] > 0)));
  requires(forall(0, xss.length, ((i) => xss[i].length === 0 || xss[i][0] > 0)));
  requires(xss.some(((r) => r.length === 0 || r[0] > 0)) || exists(0, xss.length, ((i) => xss[i].length === 0 || xss[i][0] > 0)) || xss.length === 0);
  return xss.length > 0;
}
