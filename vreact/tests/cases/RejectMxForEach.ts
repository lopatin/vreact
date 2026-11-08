// expect: reject forEach is not supported
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>): int {
  let s = 0;
  m.forEach((v) => console.log(v));
  return s;
}
