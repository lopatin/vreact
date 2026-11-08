// expect: reject src/RnTsIgnore.ts:10: `@ts-ignore` is not supported
// The translation reads TypeScript's types to tell null from undefined; the line-level
// suppression comment below silenced the error of `const x: int | undefined = null`, so
// `x === undefined` was decided true and f's contract proved (formerly VERIFIED), while JS
// returns 2.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  // @ts-ignore
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
