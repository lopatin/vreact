// expect: reject module path clash: src/Lib/x.ts and src/lib.ts put their generated Lean into the directories VTS/Lib/ and VTS/lib/
// src/lib.ts (module VTS.lib, files in VTS/lib/) and src/Lib/x.ts (VTS.Lib.x, in VTS/Lib/x/):
// on a case-insensitive disk both land in one directory, and Lean's messages name
// VTS/Lib/x/Defs.lean while the file on disk is VTS/lib/x/Defs.lean (before: clamp2's
// obligation was "not checked" and reported as "pending (hole() / sorry)").
import { ensures, type int } from "vreact/spec";
export function clamp(x: int): int {
  ensures((r: int) => 0 <= r && r <= 100);
  return x < 0 ? 0 : x > 100 ? 100 : x;
}
