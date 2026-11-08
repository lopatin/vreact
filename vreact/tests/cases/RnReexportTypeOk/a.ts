// expect: verified verdict=verified f=verified mk=verified
// Re-exports of types written as such are erased by every compiler: accepted.
import { type int, ensures } from "vreact/spec";
import { type Item, mk } from "./types";

export type { Item };
export { type Item as Item2, mk } from "./types";

export function f(x: int): int {
  ensures((r) => r === x);
  const it: Item = mk(x);
  return it.id;
}
