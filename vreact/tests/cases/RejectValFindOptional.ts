// expect: reject find on an array of optional values
// [null].find(...) is null (found) but [].find(...) is undefined: one Option cannot tell them apart
// (and `?? d` / `== null` treat both alike, so a nested Option would be wrong too).
import { type int } from "vreact/spec";

export function firstOrDefault(xs: readonly (int | null)[]): int {
  return xs.find((x) => x === null) ?? 0;
}
