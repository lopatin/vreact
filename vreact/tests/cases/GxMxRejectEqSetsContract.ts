// expect: reject === on ReadonlySet<K> compares object identity in JS
// The same in a contract of a generic Set helper.
import { ensures, type int } from "vreact/spec";

export function copyOf<K extends int | string>(s: ReadonlySet<K>): ReadonlySet<K> {
  ensures((r: ReadonlySet<K>) => r !== s);
  return new Set(s);
}
