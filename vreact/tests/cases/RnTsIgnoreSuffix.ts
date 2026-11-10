// expect: reject src/RnTsIgnoreSuffix.ts:10: `@ts-ignore` is not supported
// TypeScript matches its line directives as prefixes (no end anchor), so a suppression comment
// followed by more letters still silences the error of the next line: here the error of
// `const x: int | undefined = null` (formerly VERIFIED with r === 1, while JS returns 2).
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  // (the directive spelled with a trailing "d")
  // @ts-ignored
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
