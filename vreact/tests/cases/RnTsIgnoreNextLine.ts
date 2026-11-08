// expect: reject src/RnTsIgnoreNextLine.ts:9: `@ts-ignore` is not supported
// The block-comment form with a suffix (TypeScript reads the last line of a block comment with
// `/^(?:\/|\*)*\s*@(ts-expect-error|ts-ignore)/`): formerly VERIFIED with r === 1, while JS
// returns 2.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  /* @ts-ignore-next-line */
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
