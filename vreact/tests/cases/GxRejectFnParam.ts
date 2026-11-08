// expect: reject parameter p is a function ((x: T) => boolean): a top-level function cannot take a callback
// A predicate parameter: functions are not data in VTS (it crashed the translator before).
import { type int } from "vreact/spec";

export function findOr<T>(xs: readonly T[], p: (x: T) => boolean, d: T): T {
  const f = xs.find((x) => p(x));
  return f === undefined ? d : f;
}
