// expect: verified index=verified tags=verified total=verified evens=verified ids=verified unique=verified pairs=verified errors=none
import { distinct, ensures, type int } from "vreact/spec";

export type Order = { readonly id: int; readonly qty: int; readonly tag: string };

// a Map built by a loop (n.set in for…of)
export function index(xs: readonly Order[]): ReadonlyMap<int, Order> {
  ensures((r) => xs.every((x) => r.has(x.id)));
  const n = new Map<int, Order>();
  for (const x of xs) n.set(x.id, x);
  return n;
}

// a Set built by a loop
export function tags(xs: readonly Order[]): ReadonlySet<string> {
  ensures((r) => xs.every((x) => r.has(x.tag)));
  const s = new Set<string>();
  for (const x of xs) s.add(x.tag);
  return s;
}

// for…of over the entries, destructured
export function total(m: ReadonlyMap<int, Order>): int {
  let sum = 0;
  for (const [k, o] of m) {
    if (k === o.id) sum += o.qty;
  }
  return sum;
}

// for…of over the keys and a Set
export function evens(m: ReadonlyMap<int, string>, s: ReadonlySet<int>): int {
  let c = 0;
  for (const k of m.keys()) {
    if (k % 2 === 0) c++;
  }
  for (const x of s) {
    if (x > 0) c += 1;
  }
  return c;
}

export function ids(m: ReadonlyMap<int, Order>): readonly int[] {
  ensures((r) => distinct(r));
  return Array.from(m.keys());
}

export function unique(xs: readonly string[]): readonly string[] {
  ensures((r: readonly string[]) => distinct(r) && r.every((x) => xs.includes(x)));
  return [...new Set(xs)];
}

// a Map from computed pairs, read back in a loop over its entries
export function pairs(xs: readonly Order[]): readonly [int, int][] {
  ensures((r: readonly [int, int][]) => r.every(([k, q]) => k >= q - q));
  const m = new Map<int, int>(xs.map((x: Order) => [x.id, x.qty]));
  let out: readonly [int, int][] = [];
  for (const e of m.entries()) out = [...out, e];
  return out.filter(([k, q]) => k >= q - q);
}
