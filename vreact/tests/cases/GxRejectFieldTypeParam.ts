// expect: reject it mentions a type parameter
// A field constraint's field types must not mention type parameters (no recursive constraints).
import { ensures, requires, type int } from "vreact/spec";

export function first<T extends { readonly next: readonly T[] }>(x: T): int {
  return x.next.length;
}
