// expect: reject proofs/m.lean:2:1: `import Lean` is not allowed in a proof file ;; proofs/m.lean:3:1: `import Std.Tactic.BVDecide` is not allowed
// Imports of a user proof (R4 item 12): only the generated modules (VTS.…), other proof files
// (Proofs.…) and the library (VReact, VReact.…). Other modules bring syntax, instances and
// attributes the whitelist check (which parses the file in the environment it is elaborated
// in) does not know about.
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
