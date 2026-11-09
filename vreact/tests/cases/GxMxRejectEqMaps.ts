// expect: reject === on ReadonlyMap<K, V> compares object identity in JS
// === on Maps compares identity, also in generic code (a copy with the same entries differs).
import { type int } from "vreact/spec";

export function same<K extends int | string, V>(a: ReadonlyMap<K, V>, b: ReadonlyMap<K, V>): boolean {
  return a === b;
}
