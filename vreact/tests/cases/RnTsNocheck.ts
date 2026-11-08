// expect: reject src/RnTsNocheck.ts:2: `@ts-nocheck` is not supported
// @ts-nocheck
// The file-level directive turns TypeScript's checks off for the whole file (here: a string
// where an int | null is declared). Rejected like the line-level ones.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  const x: int | null = "a";
  return x === null ? 0 : 1;
}
