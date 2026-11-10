// expect: reject "out" ("proofs/build") is inside the "proofs" directory
// The generated Lean inside "proofs": the next run reads it as user proofs.
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
