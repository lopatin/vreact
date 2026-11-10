// expect: synth inc=x~+~1 out=cut~off~(its~tests~take~longer~than~5s)~after~passing noout=no~candidate~passed~the~tests
// synth round 2: every test evaluates slowInc (in the contract), so every candidate's tests take
// longer than the 5 s that one candidate gets; such a candidate was dropped although it passed every
// test that ran, and synth ended with "no candidate passed the tests ... check that the spec is
// satisfiable" (x + 1 was proved before the cap existed). A candidate cut off after passing tests is
// now tried by Lean after the candidates whose tests finish (once 3 are held back, or at the end).
import { requires, ensures, range, hole, type int } from "vreact/spec";

export function slowInc(n: int): int {
  requires(n >= 0);
  ensures((r: int) => r === n + 1);
  let c = 0;
  for (const i of range(n)) {
    for (const j of range(n)) {
      c = c + i * j;
    }
  }
  return n + 1;
}

export function inc(x: int): int {
  requires(x >= 0 && x <= 3000);
  ensures((r: int) => r === slowInc(x));
  return hole<int>();
}
