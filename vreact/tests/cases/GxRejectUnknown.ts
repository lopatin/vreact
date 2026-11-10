// expect: reject it constrains nothing
// `extends unknown` is no constraint: leave it out.
import { ensures, requires, type int } from "vreact/spec";

export function id<T extends unknown>(x: T): T {
  return x;
}
