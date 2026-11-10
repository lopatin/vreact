// expect: fail assert faildesc=assertion~label~!==~"a~~~b"
// The description of an obligation keeps the contents of a string literal exact ("a   b" was
// shown as "a b": whitespace is collapsed only outside literals).
import { assert } from "vreact/spec";

export function check(label: string): string {
  assert(label !== "a   b");
  return label;
}
