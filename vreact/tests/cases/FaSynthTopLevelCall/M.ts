// expect: synth inc=x~+~1 dec=x~-~1 noout=does~not~load
// synth-r1-1: module-level code that calls the module's functions runs when the module loads,
// also in synth's tests. TEN calls inc itself (whose own contract the tests rename): every
// candidate failed with "does not load: __vreactOwnEnsures__ is not defined". NINE calls dec,
// which still has a hole while inc is searched: every candidate of inc failed with "does not
// load: vreact: unfilled hole()". Now the top-level code runs in test mode, a hole stops it, and
// the inputs that read what it never initialized are skipped.
import { ensures, hole, type int } from "vreact/spec";

export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}

export function dec(x: int): int {
  ensures((r: int) => r === x - 1);
  return hole<int>();
}

export const TEN: int = inc(9);
export const NINE: int = dec(10);
