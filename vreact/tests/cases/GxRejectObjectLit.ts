// expect: reject an object literal is not a value of the type parameter T
// A value of T cannot be built from an object literal (T may have more fields).
import { ensures, requires, type int } from "vreact/spec";

export function withId<T extends { readonly id: int }>(x: T): T {
  return { ...x, id: 0 };
}
