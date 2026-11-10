// expect: synth write inc=x~+~1 dec=x~-~1 noout=does~not~translate written=import~type~{~Other~}~from~"./types"; written=export~type~Kept~=~int; absent=type~Local~=~int;
// synth-r1-4: under noUnusedLocals, a type used only as a hole's type argument (`hole<Count>()`)
// loses its last use when the hole is filled: every candidate failed to translate (TS6133), "a
// synth limitation". Synth drops such a type import, or a type of the file's own that is not
// exported (Local), as it drops the `hole` import; what is still used (Other) or exported (Kept) stays.
import { ensures, hole, type int } from "vreact/spec";
import type { Count, Other } from "./types";

type Local = int;
export type Kept = int;

export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<Count>();
}

export function dec(x: Other): Other {
  ensures((r: int) => r === x - 1);
  return hole<Local>();
}
