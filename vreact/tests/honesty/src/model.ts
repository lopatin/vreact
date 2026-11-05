// Fixture of the report-honesty checks (tests/honesty.ts): verified as it is; the checks
// doctor Lean's output and require that the report then never says VERIFIED.
import { assert, ensures, type int } from "vreact/spec";
/** @opaque */
export const LIMIT: int = 10;
assert(LIMIT > 0);
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
/** @opaque */
export function clamp(x: int): int {
  ensures((r: int) => 0 <= r && r <= LIMIT);
  return x < 0 ? 0 : x > LIMIT ? LIMIT : x;
}
