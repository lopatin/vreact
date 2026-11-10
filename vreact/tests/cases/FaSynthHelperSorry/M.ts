// expect: synth inc=x~+~1 out=candidates~that~do~not~call~it~are~tried~next
// synth-r1-3: the helper next has a failed obligation (its assert cannot be proved), which Lean
// admits with a sorry. The first candidate that passed the tests, next(x), was "pending" because
// of that sorry, and synth stopped the whole search ("no candidate of this function can be
// checked now"), so x + 1, which Lean proves, was never tried. A sorry that comes from a helper
// the candidate itself calls now rules out only the candidates calling it.
import { ensures, assert, hole, type int } from "vreact/spec";

export function next(x: int): int {
  assert(x !== 999);
  return x + 1;
}

export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}
