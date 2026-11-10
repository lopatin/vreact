// expect: reject parameter m has the function type (x: int) => int (field f of Box), which is not data
// A record with a function field as a Map value: not data, as for an array of it (the record is
// not emitted, so the generated Lean failed with "Unknown identifier" before).
import { ensures, type int } from "vreact/spec";

type Box = { readonly f: (x: int) => int; readonly n: int };

export function g(m: ReadonlyMap<int, Box>): int {
  ensures((r) => r >= 0);
  return m.size;
}
