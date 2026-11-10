import { type int, ensures } from "vreact/spec";

export function maxQty(): int {
  ensures((r) => r > 0);
  return 5;
}
