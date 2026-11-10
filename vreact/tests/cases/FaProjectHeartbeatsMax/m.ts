// expect: verified verdict=verified
// The largest "heartbeats" vreact.json accepts: the budgets are written as decimal numerals.
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
