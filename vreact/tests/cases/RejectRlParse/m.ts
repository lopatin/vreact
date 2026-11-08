// expect: reject proofs/Base.lean:4:1: the proof file does not parse
// A user proof that does not parse (R4 item 12): the whitelist check reads it with Lean's own
// parser and accepts only what it parsed completely (Lean's error recovery resumes at the next
// command keyword, where the check could not know what Lean will see).
import { ensures, type int } from "vreact/spec";
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return x + 1;
}
