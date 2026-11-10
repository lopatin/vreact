// expect: verified amendBoth=verified amendFwdPred=verified amendBothInline=verified errors=none
// Frame conditions after the documented read `const o = m.get(k); if (o === undefined) return m; …`:
// through a named predicate or with both directions they timed out — `repeat' split` split the
// `match h : some p with …` that the first split left under the frame's binder again and again
// (vreact_splits reduces it after each split).
import { ensures, type int } from "vreact/spec";

export type O = { readonly id: int; readonly qty: int; readonly price: int };

export function same(a: O, b: O): boolean {
  return a.id === b.id && a.qty === b.qty && a.price === b.price;
}

/** `m` holds `o` under `k`. */
export function holds(m: ReadonlyMap<int, O>, k: int, o: O): boolean {
  const p = m.get(k);
  return p !== undefined && same(o, p);
}

/** The same entries, except perhaps at `k`. */
export function agreeExcept(a: ReadonlyMap<int, O>, b: ReadonlyMap<int, O>, k: int): boolean {
  return [...a].every(([j, o]) => j === k || holds(b, j, o)) && [...b].every(([j, o]) => j === k || holds(a, j, o));
}

// each direction alone: verified
export function amendFwd(m: ReadonlyMap<int, O>, k: int, q: int): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => [...m].every(([j, o]) => j === k || holds(r, j, o)));
  const o = m.get(k);
  if (o === undefined) return m;
  return new Map(m).set(k, { ...o, qty: q });
}

export function amendBack(m: ReadonlyMap<int, O>, k: int, q: int): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => [...r].every(([j, o]) => j === k || holds(m, j, o)));
  const o = m.get(k);
  if (o === undefined) return m;
  return new Map(m).set(k, { ...o, qty: q });
}

// both directions in one ensures
export function amendBoth(m: ReadonlyMap<int, O>, k: int, q: int): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => agreeExcept(m, r, k));
  const o = m.get(k);
  if (o === undefined) return m;
  return new Map(m).set(k, { ...o, qty: q });
}

/** One direction, as a predicate. */
export function keeps(a: ReadonlyMap<int, O>, b: ReadonlyMap<int, O>, k: int): boolean {
  return [...a].every(([j, o]) => j === k || holds(b, j, o));
}

// one direction through the predicate
export function amendFwdPred(m: ReadonlyMap<int, O>, k: int, q: int): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => keeps(m, r, k));
  const o = m.get(k);
  if (o === undefined) return m;
  return new Map(m).set(k, { ...o, qty: q });
}

// both directions inline in one ensures
export function amendBothInline(m: ReadonlyMap<int, O>, k: int, q: int): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => [...m].every(([j, o]) => j === k || holds(r, j, o)) && [...r].every(([j, o]) => j === k || holds(m, j, o)));
  const o = m.get(k);
  if (o === undefined) return m;
  return new Map(m).set(k, { ...o, qty: q });
}

// both directions, no read of the old value
export function setBoth(m: ReadonlyMap<int, O>, k: int, v: O): ReadonlyMap<int, O> {
  ensures((r: ReadonlyMap<int, O>) => agreeExcept(m, r, k));
  return new Map(m).set(k, v);
}
