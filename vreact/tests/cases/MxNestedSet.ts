// expect: verified
import { ensures, type int } from "vreact/spec";

// group membership: a Set stored inside a Map
export function mxnsJoin(g: ReadonlyMap<string, ReadonlySet<int>>, k: string, x: int): ReadonlyMap<string, ReadonlySet<int>> {
  ensures((r) => r.has(k) && r.get(k)!.has(x));
  const cur = g.get(k) ?? new Set<int>();
  return new Map(g).set(k, new Set(cur).add(x));
}

export function mxnsJoin2(g: ReadonlyMap<string, ReadonlySet<int>>, k: string, x: int): ReadonlyMap<string, ReadonlySet<int>> {
  ensures((r) => r.has(k) && r.get(k)!.has(x));
  const s = new Set(g.get(k) ?? new Set<int>());
  s.add(x);
  return new Map(g).set(k, s);
}

// leave the group (and drop it when it becomes empty)
export function mxnsLeave(g: ReadonlyMap<string, ReadonlySet<int>>, k: string, x: int): ReadonlyMap<string, ReadonlySet<int>> {
  ensures((r) => !r.has(k) || !r.get(k)!.has(x));
  const cur = g.get(k);
  if (cur === undefined) return g;
  const s = new Set(cur);
  s.delete(x);
  const n = new Map(g);
  if (s.size === 0) n.delete(k);
  else n.set(k, s);
  return n;
}
