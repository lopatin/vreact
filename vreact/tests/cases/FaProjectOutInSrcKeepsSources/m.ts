// expect: reject src/gen/VTS/Keep.ts is not a file vreact generated
// "out" inside "src" is accepted, but vreact replaces <out>/VTS and <out>/Proofs only when they
// hold nothing but Lean files: the source src/gen/VTS/Keep.ts is never removed.
import { type int } from "vreact/spec";

export const M: int = 1;
