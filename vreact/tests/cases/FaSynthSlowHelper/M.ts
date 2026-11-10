// expect: synth inc=x~+~1 out=cut~off~(its~tests~take~longer~than~5s)~after~passing noout=proved~by~Lean:~slowInc(x)
// synth-r1-6: a candidate's random tests ran to the end with no time limit (the limit was only
// checked between candidates): slowInc(x), whose cost grows with the 8000 the contract allows,
// took more than 3 minutes to test, against the 60 s per hole. One candidate's tests now get at
// most 5 s, and never more than the search has left; the search goes on, and a candidate cut off
// after passing the tests that ran (slowInc(x)) goes to Lean only after the candidates whose tests
// finish (x + 1, proved first).
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
