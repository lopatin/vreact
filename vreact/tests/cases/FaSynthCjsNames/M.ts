// expect: synth inc=x~+~1 noout=does~not~load
// synth round 2: synth runs a candidate's module as a CommonJS function whose parameters are
// `exports`, `require`, `module`, `__filename` and `__dirname`. A module-level binding so named, legal
// in an ES module (the program translates), redeclared a parameter (`const module`: a SyntaxError)
// or replaced the exports object (`const exports`): every candidate failed with "does not load".
// The wrapper's parameters no longer meet the module's own names, here and in the dependency lib
// (whose exports keep their names).
import { ensures, hole, type int } from "vreact/spec";
import { require as one, module as zero } from "./lib";

export const module: int = 1;
const exports: int = 0;
const require: int = 0;
const __filename: int = 0;
const __dirname: int = 0;

export function inc(x: int): int {
  ensures((r: int) => r === x + module + exports + require + __filename + __dirname + one - 1 + zero);
  return hole<int>();
}
