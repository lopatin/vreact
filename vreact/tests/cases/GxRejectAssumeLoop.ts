// expect: reject assume(…) is not supported in a for…of loop body
// A for…of body is checked as a fold step for every accumulator and element (as its
// obligations are: the loop forgets what it knows about the variables it assigns), so the
// theorem Lean keeps of this assume(…) would be `∀ s, s ≥ 0` — false (at -1), although the
// fact holds whenever the loop runs (s counts up from 0). A user proof could derive False
// from it without naming VReact.assumed.
import { assume, type int } from "vreact/spec";

export function count(xs: readonly int[]): int {
  let s = 0;
  for (const x of xs) {
    assume(s >= 0);
    s = s + 1;
  }
  return s;
}
