// expect: verified verdict=verified inc=verified proved=2 errors=none
// A file name is not VTS code: src/_hyg.ts was the namespace VTS._hyg, which Lean takes for a
// macro-scoped name (its declarations were lost, Lean panicked); a segment starting with `_` or a
// digit now gets a leading M (VTS.M_hyg, VTS.M_x.M1y).
import { ensures, type int } from "vreact/spec";
import { dec } from "./_x/1y";

export function inc(x: int): int {
  ensures((r) => r > dec(x));
  return x + 1;
}
