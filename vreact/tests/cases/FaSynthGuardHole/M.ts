// expect: synth relu=x~<~0 relu#2=0 noout=no~generated~input~can~test~this~hole~(
// synth-r1-5: the first candidate of the guard hole, `true`, sends every input to the unfilled
// second hole, and synth concluded that no input can test the guard hole at all (for every later
// candidate too): `false` and `!true` went to Lean untested, and the search stopped after three
// such fills, never reaching `x < 0`, which the tests can check. Whether an input reaches the
// other hole depends on the candidate here: the candidates no input can test are now tried after
// the ones that pass the tests.
import { ensures, hole, type int } from "vreact/spec";

export function relu(x: int): int {
  ensures((r: int) => r >= 0 && (x >= 0 ? r === x : r === 0));
  if (hole<boolean>()) return hole<int>();
  return x;
}
