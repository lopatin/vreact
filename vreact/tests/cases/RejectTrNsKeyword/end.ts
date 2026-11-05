// expect: reject module name clash
// end.ts becomes VTS.end_ (`end` is a Lean keyword), the module name of end_.ts.
import { type int } from "vreact/spec";
export function one(): int {
  return 1;
}
