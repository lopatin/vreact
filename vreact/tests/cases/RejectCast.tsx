// expect: reject unchecked casts
import { type int } from "vreact/spec";
export function half(x: number): int {
  return (x / 2) as int;
}
