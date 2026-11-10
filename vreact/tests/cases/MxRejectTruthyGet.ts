// expect: reject `m.get(1)` is number | undefined, and a boolean is needed here: JS would test its truthiness
// `m.get(k) || d` on number values: the message shows the nullish value (undefined) and what to
// write (it said "type mismatch: expected boolean, got number | null").
import { type int } from "vreact/spec";

export function f3(m: ReadonlyMap<int, number>): number {
  return m.get(1) || 5;
}
