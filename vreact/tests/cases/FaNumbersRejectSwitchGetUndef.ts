// expect: reject switch on a value of type int | undefined is not supported
// A Map's get() is `int | undefined`, never null (finding mapset-r1-2: shown as `int | null`).
import { ensures, type int } from "vreact/spec";

export function f(m: ReadonlyMap<int, int>): int {
  ensures((r: int) => r === 0 || m.get(1) === 1);
  switch (m.get(1)) {
    case 1:
      return 1;
    default:
      return 0;
  }
}
