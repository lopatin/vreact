// expect: verified
// A contract's every/some/forall/exists whose callback is read as code (a block body, a
// `function (x) { … }`) translates its receiver and bounds once: the index obligations of
// `xss[0]` (a receiver) and of `xss[1]` (in a bound) are registered once.  A second translation
// before choosing between the quantifier and the code reading would leave an obligation that
// the generated Lean does not contain (reported as not checked: "missing from the generated Lean").
import { requires, ensures, forall, exists, type int } from "vreact/spec";

export function head(xss: readonly (readonly int[])[]): int {
  requires(xss.length > 0 && xss[0].length > 0 && xss[0].every((x) => { return x > 0; }));
  ensures((r: int) => r > 0);
  return xss[0][0];
}

export function second(xss: readonly (readonly int[])[]): int {
  requires(xss.length > 1 && xss[1].length > 0 && xss[1].some(function (x) { return x > 0; }));
  requires(forall(0, xss[1].length, (k) => { return k >= 0; }) && exists(0, xss[1].length + 1, function (k) { return k === 0; }));
  return xss[1][0];
}
