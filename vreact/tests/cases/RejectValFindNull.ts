// expect: reject can be undefined but never null
// find() returns undefined when nothing matches: `=== null` is always false (also in contracts).
import { ensures, type int } from "vreact/spec";

export function notFound(xs: readonly int[], k: int): boolean {
  ensures((r) => r === (xs.find((x) => x === k) === null));
  return !xs.includes(k);
}
