// expect: reject "out" (".") is the project directory itself
// vreact removes <out>/VTS and <out>/Proofs before writing the generated Lean: with "out": "."
// that was ./proofs on a case-insensitive disk (and ./vts with "src": "vts"), the user's files.
import { type int, ensures } from "vreact/spec";

export function inc(x: int): int {
  ensures((r) => r > x);
  return x + 1;
}
