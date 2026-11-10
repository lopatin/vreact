import { type int, ensures } from "vreact/spec";
export function inc(x: int): int {
  ensures((r) => r === x + 1);
  return x + 1;
}
