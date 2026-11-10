// expect: reject is a Set or an array in JS: give a Set as the default (m.get(k) ?? new Set<E>()), or iterate it at once
// `m.get(k) ?? []` kept as a value (not iterated at once) mixes a Set and an array: the message
// says what to write (it said "empty array literal needs a known element type (annotate it)").
import { type int } from "vreact/spec";

export function setOf<K extends int | string, E extends int | string>(m: ReadonlyMap<K, ReadonlySet<E>>, k: K, e: E): boolean {
  const s = m.get(k) ?? [];
  return new Set(s).has(e);
}
