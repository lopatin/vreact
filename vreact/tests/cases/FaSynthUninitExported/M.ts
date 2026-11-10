// expect: synth inc=x~+~1 always=- noout=postcondition~fails~on~[6] out=no~generated~input~could~test~the~last~50~candidates
// synth round 2: synth runs a candidate's module as CommonJS, where TypeScript reads an exported
// constant as `exports.STEP`: when the module's top-level code stopped before STEP's declaration
// (here at the hole of the @trusted stub seed, which synth never fills), STEP read as undefined
// instead of throwing a ReferenceError as in an ES module, so the inputs that read it were not
// skipped: `x + 1` failed on x = 6 (`7 === 6 + undefined`), a false counterexample, and so did
// every candidate. Exported constants now keep their ES meaning: inc is tested on the inputs that
// do not read STEP; always, whose every input reads it, is a hole no input can test.
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

export function always(x: int): int {
  ensures((r: int) => r === x + STEP);
  return hole<int>();
}

export const NINE: int = seed(9);
export const STEP: int = 1;
