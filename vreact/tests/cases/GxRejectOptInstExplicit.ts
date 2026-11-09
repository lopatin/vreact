// expect: reject size: its type parameter V would be int | undefined, which includes null/undefined: a type parameter is never instantiated with a nullable type (JS has one nullish value, while V | undefined would nest two in the model); write a type argument without null/undefined (e.g. size<int>(…))
// An explicit nullable type argument: the message shows the type argument (it showed the Map's
// value type, "V would be int, which includes null/undefined") and advises a non-nullable one.
import { type int } from "vreact/spec";

export function size<V>(m: ReadonlyMap<int, V>): int {
  return m.size;
}

export function use(m: ReadonlyMap<int, int>): int {
  return size<int | undefined>(m);
}
