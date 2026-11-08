// expect: reject src/RnTsNocheckCase.ts:2: `@TS-NOCHECK` is not supported
// @TS-NOCHECK
// TypeScript lower-cases the names of the pragmas in a file's leading comments, so the
// upper-case spelling above turns off every check of the file: formerly VERIFIED with
// r === 1, while JS returns 2.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
