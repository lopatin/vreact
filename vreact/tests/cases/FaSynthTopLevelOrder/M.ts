// expect: synth inc=x~+~1 dec=x~-~1
// synth round 2: the module's top-level code calls dec, so while dec has a hole that code stops
// there in synth's tests, and STEP, declared after it, is never initialized: inc, searched first,
// could not be tested by any input (its contract reads STEP) and was left unfilled although x + 1
// is proved. The functions that the top-level code runs are now filled first.
import { ensures, hole, type int } from "vreact/spec";

export function inc(x: int): int {
  ensures((r: int) => r === x + STEP);
  return hole<int>();
}

export function dec(x: int): int {
  ensures((r: int) => r === x - 1);
  return hole<int>();
}

export const NINE: int = dec(10);
export const STEP: int = 1;
