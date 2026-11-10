// expect: reject keysOf: its type parameter K would be number: K has an equality constraint
// The same with explicit type arguments on a Map helper.
import { type int } from "vreact/spec";

export function keysOf<K extends int | string, V>(m: ReadonlyMap<K, V>): readonly K[] {
  return [...m.keys()];
}

export function ks(m: ReadonlyMap<int, string>): int {
  return keysOf<number, string>(m).length;
}
