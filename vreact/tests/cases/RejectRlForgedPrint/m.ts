// expect: reject proofs/m.lean:3:8: a string, character or name literal with a line break ;; proofs/m.lean:8:9: a string, character or name literal with a line break ;; proofs/m.lean:12:16: a string ;; proofs/m.lean:12:72: a string ;; proofs/m.lean:14:9: a name with a line break ;; proofs/m.lean:17:8: a string, character or name literal ;; proofs/m.lean:20:23: a string, character or name literal
// A user proof printed lines that the report read as Lean's messages about a generated file
// (round-1 finding r4-lean-forge-print): `#print "x\ninfo: VTS/m/Posts.lean:14:16: vreact:ok"`
// (and the `trace`/`fail` tactics, a name «…» with a line break in an error) — lake prints a
// message's text as it is, so its second line looked like the obligation's positive evidence,
// the sentinel or an axiom report. Two fixes: the report takes an info about a generated file
// only from the job log of that file's module (tests/run.ts, "parseMessages"), and proof files
// may not contain line breaks (or other control characters) in string, character and name
// literals (also as escapes `\n`, `\u000a`, `\x0d`, in interpolated strings) or names. A
// one-line string, or a raw string with a backslash, is fine (the last two #print).
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 2);
  return x + 1;
}
