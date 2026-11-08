// expect: reject tsconfig: "noCheck" is not supported
// TypeScript 5.5's "noCheck" reports no type error at all: `const x: int | undefined = null`
// type-checked, `x === undefined` was decided true and the contract below proved (formerly
// VERIFIED), while JS returns 2.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
