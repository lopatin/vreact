// expect: reject src/RnTsExpectErrorSuffix.ts:8: `@ts-expect-error` is not supported
// `@ts-expect-errors` (a suffix after the directive) is still the directive for TypeScript:
// formerly VERIFIED with r === 1, while JS returns 2.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  // @ts-expect-errors
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
