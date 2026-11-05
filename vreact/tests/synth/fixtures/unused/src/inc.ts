import { ensures, hole, type int } from "vreact/spec";

// filling the last hole leaves `hole` unused (TS6133 under noUnusedLocals): synth drops the import
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}
