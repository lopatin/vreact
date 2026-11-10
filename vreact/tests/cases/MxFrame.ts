// expect: verified setPrice=verified rename=verified dropKey=verified toggle=verified keysOf=verified grow=verified sizes=verified errors=none
import { distinct, ensures, requires, type int } from "vreact/spec";

// Map/Set updates: frame conditions (what does not change), sizes, membership
export function setPrice(m: ReadonlyMap<int, int>, k: int, v: int): ReadonlyMap<int, int> {
  ensures((r) => r.get(k) === v);
  ensures((r) => r.has(k) && r.size >= m.size && r.size <= m.size + 1);
  ensures((r) => [...m.keys()].every((j) => j === k || r.get(j) === m.get(j)));
  return new Map(m).set(k, v);
}

export function rename(m: ReadonlyMap<string, int>, k: string, k2: string, v: int): ReadonlyMap<string, int> {
  ensures((r) => r.get(k2) === v);
  ensures((r) => k === k2 || !r.has(k));
  const n = new Map(m);
  n.delete(k);
  n.set(k2, v);
  return n;
}

export function dropKey(m: ReadonlyMap<int, string>, k: int): ReadonlyMap<int, string> {
  requires(m.has(k));
  ensures((r: ReadonlyMap<int, string>) => r.size + 1 === m.size && r.get(k) === undefined);
  ensures((r) => [...r.keys()].every((j) => m.has(j)));
  const n = new Map(m);
  n.delete(k);
  return n;
}

export function toggle(s: ReadonlySet<int>, x: int): ReadonlySet<int> {
  ensures((r) => r.has(x) === !s.has(x));
  ensures((r) => [...s].every((y) => y === x || r.has(y)));
  const n = new Set(s);
  if (n.has(x)) n.delete(x);
  else n.add(x);
  return n;
}

export function keysOf(m: ReadonlyMap<int, string>): readonly int[] {
  ensures((r) => distinct(r) && r.length === m.size);
  return [...m.keys()];
}

// values: an invariant of every value survives a set of a value that satisfies it
export function grow(m: ReadonlyMap<string, int>, k: string, d: int): ReadonlyMap<string, int> {
  requires([...m.values()].every((v) => v >= 0));
  requires(d >= 0);
  ensures((r) => [...r.values()].every((v) => v >= 0));
  return new Map(m).set(k, (m.get(k) ?? 0) + d);
}

export function sizes(m: ReadonlyMap<int, int>, a: int, b: int): int {
  requires(!m.has(a) && !m.has(b) && a !== b);
  ensures((r) => r === m.size + 2);
  const n = new Map(m);
  n.set(a, 1);
  n.set(b, 2);
  n.set(a, 3);
  return n.size;
}
