// expect: reject by identity
import { type int } from "vreact/spec";

export function f(): int {
  const s = new Set<[int, int]>();
  return s.size;
}
