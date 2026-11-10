// expect: reject function overloads (declarations without a body) are not supported
import { type int } from "vreact/spec";

export function f(x: int): int;
export function f(x: int): int {
  return x + 1;
}
