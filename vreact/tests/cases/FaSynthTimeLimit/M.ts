// expect: synth seconds=2 inc=- out=time~limit~was~reached~at~size~2,~while~slowInc(x)~was~tested maxsecs=90
// synth-r1-6: the search's time limit holds while a candidate is tested (here 2 s, so slowInc(x)
// is cut off and the search stops), instead of only between candidates.
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
