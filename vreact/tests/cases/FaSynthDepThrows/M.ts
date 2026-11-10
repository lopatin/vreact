// expect: synth inc=- out=it~throws:~vreact:~unfilled~hole() noout=postcondition~fails noout=x~passes~the~tests
// synth round 2 (a path no case reached): the top-level code of the dependency lib throws (it runs
// into the hole of lib's base), so the import stops M's top-level code and no input can test inc.
// As in Node, a module whose top-level code throws is not cached: every candidate's import runs it
// again and fails the same way, instead of the later candidates reading a half-initialized lib (K
// undefined: `x + K` is NaN, a false counterexample). (The untested candidate Lean is then asked
// about is not said to pass the tests.)
import { ensures, hole, type int } from "vreact/spec";
import { K } from "./lib";

export function inc(x: int): int {
  ensures((r: int) => r === x + K);
  return hole<int>();
}
