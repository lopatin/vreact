// expect: reject compares object identity
import { type int } from "vreact/spec";

import { ensures } from "vreact/spec";
export function copy(a: ReadonlySet<int>): ReadonlySet<int> {
  ensures((r) => r !== a);
  return new Set(a);
}
