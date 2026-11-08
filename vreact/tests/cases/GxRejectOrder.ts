// expect: reject an ordering comparison (<, <=, >, >=) on a value of the type parameter K
// Ordering is not available on a type parameter.
import { ensures, requires, type int } from "vreact/spec";

export function less<K extends int | string>(a: K, b: K): boolean {
  return a < b;
}
