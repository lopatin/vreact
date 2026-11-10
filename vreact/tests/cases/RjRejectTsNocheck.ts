// expect: reject `@ts-nocheck` is not supported
// @ts-nocheck
// The directive above silences every TypeScript error of the file (here: a string passed as an
// int), on which the translation relies.
import { ensures, type int } from "vreact/spec";

export function twice(x: int): int {
  ensures((r: int) => r === x + x);
  return x + x;
}

export function g(): int {
  return twice("3");
}
