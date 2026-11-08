// expect: reject tsconfig: VTS requires "strict": true, with strictFunctionTypes
// Every check of the strict family is required, not only strictNullChecks and noImplicitAny:
// without strictFunctionTypes TypeScript compares callback parameters bivariantly and accepts
// `(x: int) => …` where a callback receiving `int | null` is expected.
import { type int, ensures } from "vreact/spec";

const XS: readonly (int | null)[] = [null, 1];

export function f(): boolean {
  ensures((r) => r === true);
  return XS.map((x: int) => x + 1).every((y) => y >= 1);
}
