// expect: synth add2=x~+~1~+~1 add2#2=x~+~1~+~1 out=fills~of~hole~1~that~do~not~call~it~are~tried~next noout=it~calls~next
// synth round 2: the helper next has a failed obligation (its assert), so a proof through it rests on
// a sorry. Hole 1's first fills (next(next(x)), next(x + 1), next(x) + 1) call next; for each,
// hole 2's candidates were blamed for calling next ("it calls next", false for x + 1 + 1) and the
// three tentative fills of hole 1 ran out: nothing was filled although x + 1 + 1 in both branches
// is proved. The fill that calls the helper is now the one ruled out, in whichever hole it is.
import { ensures, assert, hole, type int } from "vreact/spec";

export function next(x: int): int {
  assert(x !== 999);
  return x + 1;
}

export function add2(x: int): int {
  ensures((r: int) => r === x + 1 + 1);
  if (x > 0) return hole<int>();
  return hole<int>();
}
