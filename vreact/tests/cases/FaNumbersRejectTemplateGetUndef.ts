// expect: reject cannot convert int | undefined to a string
// A Map's get() is `int | undefined`, never null (finding mapset-r1-2: shown as `int | null`).
import { type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>): string {
  return `${m.get(1)}`;
}
