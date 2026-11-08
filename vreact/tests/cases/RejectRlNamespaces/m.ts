// expect: reject proofs/Base.lean:3:5: `VTS.m.bump` is not allowed in a proof file: the namespaces VTS and VReact ;; proofs/Base.lean:4:1: `namespace VReact.JS` ;; proofs/Base.lean:5:9: `VReact.JS.remZero` ;; proofs/m.lean:4:9: `VTS.m.bump.post2` ;; proofs/m.lean:5:1: `namespace VTS.m` ;; proofs/m.lean:7:9: `VReact.foo` ;; proofs/m.lean:8:17: `VTS.m.priv` ;; proofs/m.lean:9:5: `JS.eq` is not allowed in a proof file: the generated code opens VReact ;; proofs/m.lean:10:1: `export List (map)` ;; proofs/m.lean:12:9: `VTS.x`
// Declarations of a user proof in the namespaces of the generated code and the library
// (R4 item 12): `def VTS.m.bump` pre-empts the generated bump (whose body violates its
// ensures), `VTS.m.bump.post2` would be used by vreact_contracts as a contract of bump,
// `namespace VReact.…` adds names the generated code resolves through `open VReact`, `JS.eq`
// makes the generated `JS.eq` ambiguous, `export` adds aliases. All are rejected before Lean
// runs, also with `_root_`, `private` or inside another namespace.
import { ensures, type int } from "vreact/spec";
export function bump(x: int): int {
  ensures((r: int) => r > x);
  return x - 1;
}
