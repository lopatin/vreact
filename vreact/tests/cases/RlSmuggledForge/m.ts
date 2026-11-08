// expect: status verdict=not-verified errors=proof same=unchecked proved=0 unchecked=1
// Lines printed by a proof are never Lean's messages about a generated module (round-2 finding
// r4-lean-r2-dbgtrace-forge). smuggled/m.lean (put in place after the translation: the whitelist
// rejects `dbg_trace`, RejectRlDbgTrace) prints, with one-line literals, a fake lake job line
// `✔ [9/9] Built VTS.m.Posts` followed by `vreact:ok` at same's obligation, a clean axiom report
// and the sentinel of VTS/m/Posts.lean; then it fails, so VTS.m.Posts (which imports it) is never
// built. Lake prints the proof's log with those lines at column 0, and the report's reading of
// lake's text took them for VTS.m.Posts's messages: same's obligation counted as proved, same
// VERIFIED. The report now reads each module's messages from that module's own build log (or,
// for a module whose build failed, from its own `lean --json` run), entry by entry, never from
// lake's text: VTS.m.Posts has no messages, and same's obligation is not checked.
import { ensures, type int } from "vreact/spec";

// false: same(0) is 0, not 1
export function same(x: int): int {
  ensures((r: int) => r === x + 1);
  return x;
}
