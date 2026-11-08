// expect: reject wrap: its type parameter T would be int | undefined, which includes null/undefined
// The instantiation is shown with the nullish value the argument has (undefined, not null).
import { type int } from "vreact/spec";

export function wrap<T>(x: T): readonly T[] {
  return [x];
}

export function wrapUndef(x: int | undefined): int {
  return wrap(x).length;
}
