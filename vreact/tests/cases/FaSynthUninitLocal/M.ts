// expect: synth inc=x~+~1 noout=postcondition~fails~on~[6]
// synth round 2: the module-level constant STEP is never initialized in synth's tests (the
// module's top-level code stops before it, at the hole of the @trusted stub seed, which synth never
// fills): an input that reads it throws a ReferenceError and is skipped, the others test the
// candidate. (No case reached this rule before; FaSynthUninitExported is the exported form.)
import { ensures, hole, type int } from "vreact/spec";

/** @trusted */
export function seed(x: int): int {
  ensures((r: int) => r === x);
  return hole<int>();
}

export function inc(x: int): int {
  ensures((r: int) => (x > 5 ? r === x + STEP : r === x + 1));
  return hole<int>();
}

export const NINE: int = seed(9);
const STEP: int = 1;
