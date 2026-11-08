// expect: reject ambient declarations (`declare …`) are not supported
// `declare function` has no body (formerly: "function may finish without returning a value").
import { type int } from "vreact/spec";

declare function f(x: int): int;

export function n(x: int): int {
  return f(x);
}
