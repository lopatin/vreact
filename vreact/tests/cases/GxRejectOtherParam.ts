// expect: reject it mentions a type parameter
// Constraints must be fixed types (no constraint mentioning another type parameter).
import { ensures, requires, type int } from "vreact/spec";

export function pick<T, K extends T>(x: T, k: K): T {
  return x;
}
