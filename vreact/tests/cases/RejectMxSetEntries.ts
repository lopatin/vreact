// expect: reject Set entries()
import { type int } from "vreact/spec";

export function f(s: ReadonlySet<int>): readonly (readonly [int, int])[] {
  return [...s.entries()];
}
