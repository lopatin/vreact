// expect: verified compact=verified ops=verified more=verified rotate=verified lastOf=verified distinctKeys=verified count=verified keysOf=verified
// Inside generic bodies everything that does not look into a T value works: null tests on T | null
// (a type parameter is never instantiated with a nullable type), narrowing, array methods,
// contracts with quantifiers, distinct with an equality-constrained key, local annotations and
// helper arrows mentioning T, for…of.
import { ensures, requires, forall, distinct, type int } from "vreact/spec";

export function compact<T>(xs: readonly (T | null)[]): readonly T[] {
  ensures((r: readonly T[]) => r.length <= xs.length);
  let out: readonly T[] = [];
  for (const x of xs) {
    if (x !== null) out = [...out, x];
  }
  return xs.length >= out.length ? out : [];
}

export function ops<T>(xs: readonly T[], y: T, i: int): readonly T[] {
  requires(0 <= i && i < xs.length);
  ensures((r: readonly T[]) => r.length === xs.length + 1);
  const keep = (z: T): T => z;
  const a: readonly T[] = xs.map((x) => keep(x));
  const b = a.concat([y]);
  return b.with(0, xs[i]);
}

// methods that do not compare elements (no contract: the body's own obligations)
export function more<T>(xs: readonly T[], y: T): int {
  const b = xs.slice(1).toReversed().toSorted(() => 0).filter(() => true);
  const e = b.find(() => true);
  const n = b.findIndex(() => false) + (b.some(() => true) ? 1 : 0) + (b.every(() => true) ? 1 : 0);
  return n + b.flatMap((x) => [x, y]).length + xs.reduce((acc, _x) => acc + 1, 0) + (e === undefined ? 0 : 1);
}

export function rotate<T>(xs: readonly T[]): readonly T[] {
  ensures((r: readonly T[]) => r.length === xs.length);
  ensures((r: readonly T[]) => forall(0, xs.length, (i) => xs.length < 2 || i === 0 || true));
  if (xs.length === 0) return xs;
  return [...xs.slice(1), xs[0]];
}

export function lastOf<T>(xs: readonly T[], d: T | null): T | null {
  const l = xs.at(-1);
  if (l === undefined) return d;
  return l;
}

export function distinctKeys<T extends { readonly id: int }>(xs: readonly T[]): boolean {
  ensures((r: boolean) => r === distinct(xs.map((x) => x.id)));
  return distinct(xs, (x) => x.id);
}

export function count<K extends int | string>(xs: readonly K[], k: K): int {
  ensures((r: int) => r >= 0 && r <= xs.length);
  ensures((r: int) => xs.includes(k) || r === 0);
  let n = 0;
  for (const x of xs) {
    if (x === k) n = n + 1;
  }
  return xs.includes(k) ? xs.filter((x) => x === k).length : 0;
}

export function keysOf<K extends string>(xs: readonly K[], k: K): readonly K[] {
  requires(distinct(xs));
  ensures((r: readonly K[]) => distinct(r) && !r.includes(k));
  const i = xs.indexOf(k);
  return i < 0 ? xs : xs.filter((x) => x !== k);
}
