// expect: reject ambient declarations (`declare …`) are not supported
// `declare const` states a type for a value nothing provides or checks.
import { type int } from "vreact/spec";

declare const LIMIT: int;

export function n(x: int): int {
  return x;
}
