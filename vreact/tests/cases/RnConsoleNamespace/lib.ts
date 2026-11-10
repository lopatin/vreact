import { type int, requires } from "vreact/spec";

export function log(xs: readonly int[]): int {
  requires(xs.length > 0);
  return xs[0];
}
