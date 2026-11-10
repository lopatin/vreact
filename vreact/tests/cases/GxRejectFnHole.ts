// expect: reject the hole's type has the function type (y: T) => T, which is not data
// (crashed the translator before: a function type has no Lean value type)
import { hole } from "vreact/spec";

export function idOf<T>(x: T): T {
  const g = hole<(y: T) => T>();
  return x;
}
