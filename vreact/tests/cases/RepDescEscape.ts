// expect: fail assert faildesc=assertion~label~!==~`a\\\nb`
// A template literal with an escaped backslash at the end of a line: the description shows the
// escape and the line break as written (it showed `a\b`, another escape, and another value).
import { assert } from "vreact/spec";

export function check(label: string): string {
  assert(label !== `a\\
b`);
  return label;
}
