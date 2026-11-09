// expect: fail postcondition faildesc=s.count)~&&~r.total~>=~s.total~&&~r.count~>=~0
// The description of a failed postcondition shows the whole contract when it has at most 120
// characters (before, it was cut at 70, after `(accepts(s, qty) ? s.count + 1 : s.co`, hiding
// the two conjuncts at the end).
import { ensures, type int } from "vreact/spec";

type S = { readonly count: int; readonly total: int };

function accepts(s: S, qty: int): boolean {
  return qty > 0 && s.total + qty <= 1000;
}

export function place(s: S, qty: int): S {
  ensures((r: S) => r.count === (accepts(s, qty) ? s.count + 1 : s.count) && r.total >= s.total && r.count >= 0);
  return { count: s.count + 1, total: s.total + qty };
}
