// expect: reject Map keys must be int, string, boolean or a string-literal enum, not number
import { type int } from "vreact/spec";

// the first pair's key is a number literal: no Map<number, …>
export function a(): int {
  const m = new Map([[1.5, "a"], [2, "b"]]);
  return m.size;
}
