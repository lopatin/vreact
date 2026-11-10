// expect: synth seconds=2 out=time~limit~was~reached maxsecs=150
// synth-r1-6: the search's time limit holds while a candidate is tested (here 2 s, so slowInc(x)
// is cut off and the search stops), instead of only between candidates. (If slowInc(x) passed the
// tests that ran before the cut, Lean judges it after the search, and proves it: so whether a fill
// is found depends on the machine's speed, and is not checked here.)
import { requires, ensures, range, hole, type int } from "vreact/spec";

export function slowInc(n: int): int {
  let c = 0;
  for (const i of range(n)) {
    for (const j of range(n)) {
      c = c + i * j;
    }
  }
  return n + 1;
}

export function inc(x: int): int {
  requires(x >= 0 && x <= 8000);
  ensures((r: int) => r === x + 1);
  return hole<int>();
}
