// expect: reject === on values of the type parameter T is not supported
// The same in a contract.
import { ensures, requires, type int } from "vreact/spec";

export function firstOr<T>(xs: readonly T[], d: T): T {
  ensures((r: T) => xs.length > 0 || r === d);
  if (xs.length === 0) return d;
  return xs[0];
}
