// expect: reject "heartbeats" must be an integer from 0 (no limit) to 1000000000
// 1e21 is an integer to Number.isInteger, but a template string writes it 1e+21, which Lean does
// not parse (an internal error instead of a vreact.json error).
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
