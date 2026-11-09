// expect: reject compares object identity
import { type int } from "vreact/spec";

// === on Maps compares identity: a copy is never ===
export function same(a: ReadonlyMap<int, int>, b: ReadonlyMap<int, int>): boolean {
  return a === b;
}
