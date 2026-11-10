// expect: reject lib.d.ts is part of the TypeScript program
/// <reference path="./lib.d.ts" />
// lib.d.ts carries `/// <reference no-default-lib="true"/>`, which made TypeScript (and so vreact)
// take it for the standard library: its ReadonlyArray.find overload returning `T | null` changed
// what `v === null` means, and big() was VERIFIED although find returns undefined in JS.
import { int, ensures } from "vreact/spec";

const XS: readonly int[] = [1, 2, 3];

export function big(): int | null {
  ensures((r: int | null) => r === 7);
  const v = XS.find((x) => x > 5);
  if (v !== null) return 7;
  return 7;
}
