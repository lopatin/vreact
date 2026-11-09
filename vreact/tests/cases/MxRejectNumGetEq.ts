// expect: reject === on number | undefined is not supported: narrow it first (const v = m.get(1); if (v !== undefined) …), then compare the numbers
// `m.get(k) === x` on number values: the message shows m.get(k) as `number | undefined` (it said
// `number | null` and advised `!== null`, which VTS then rejects as always true).
import { type int } from "vreact/spec";

export function f1(m: ReadonlyMap<int, number>): boolean {
  return m.get(1) === 1.5;
}
