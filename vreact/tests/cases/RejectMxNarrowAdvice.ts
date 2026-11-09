// expect: reject or name it and narrow: const v = r.get(k); if (v !== undefined)
import { ensures, type int } from "vreact/spec";

// `r` is unannotated (TypeScript gives it type any and lets r.get(k).has(x) through); the advice
// names the nullish value m.get(k) really has: undefined, not null
export function f(m: ReadonlyMap<int, ReadonlySet<int>>, k: int, x: int): ReadonlyMap<int, ReadonlySet<int>> {
  ensures((r) => r.get(k).has(x));
  return m;
}
