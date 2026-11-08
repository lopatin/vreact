// expect: reject `declare global`, `declare module` and namespaces are not supported
// A global augmentation changes the types of library declarations for the whole program (here
// a member of every array).
import { type int } from "vreact/spec";

declare global {
  interface ReadonlyArray<T> {
    head(): T;
  }
}

export function n(xs: readonly int[]): int {
  return xs.length;
}
