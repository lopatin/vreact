import { ensures, hole, type int } from "vreact/spec";

export function base(x: int): int {
  ensures((r: int) => r === x);
  return hole<int>();
}

export const K: int = base(1);
