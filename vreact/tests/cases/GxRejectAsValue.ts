// expect: reject only refers to a type
// Type parameters are not values (TypeScript).
import { ensures, requires, type int } from "vreact/spec";

export function f<T>(x: T): T {
  const y = T;
  return x;
}
