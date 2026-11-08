// expect: reject proofs/Base.lean:1:1: `import Init.Core` is not allowed in a proof file ;; not a part of the library or of Init ;; proofs/JS.lean:1:1: `import VReact.JS` is not allowed in a proof file ;; proofs/A.lean:5:15: `macro_rules | `($_ = $_) => `(True)` is not allowed in a proof file ;; proofs/C.lean:1:1: `import Proofs.D`: the proof files import each other in a cycle ;; proofs/C.lean:2:1: `import Proofs.Nope`: there is no proof file proofs/Nope.lean ;; proofs/D.lean:2:1: `import Proofs.C`: the proof files import each other in a cycle
// A proof file is checked in the environment Lean elaborates it in (round-2 finding
// r4-lean-r2-env-mismatch). The check parsed every file with imports in `Init` + `VReact`, where
// `m!` is a token (message interpolation), while Lean elaborated `import Init.Core` (or
// `import VReact.JS`, or only proof files without imports) with neither: there `m!` is an
// identifier, and `#check m! "A{"macro_rules … #check "}B"` hides a command in what the check
// read as one string. proofs/Base.lean's global `macro_rules` turned the generated `same x = x + 1`
// into `True`: same's false ensures was VERIFIED (JS.lean smuggled an axiom and an instance).
// Now a proof file may import VReact (the whole library), Init, generated modules and other proof
// files; the environment follows the imports through the proof files (A imports only B, which
// imports nothing: A is checked in Init, and its macro_rules is seen); a missing proof module or
// an import cycle is reported. The kernel re-check of what each proof module added is the
// backstop (RlSmuggledMacro, RlSmuggledInstance).
import { ensures, type int } from "vreact/spec";

// false: same(0) is 0, not 1
export function same(x: int): int {
  ensures((r: int) => r === x + 1);
  return x;
}
