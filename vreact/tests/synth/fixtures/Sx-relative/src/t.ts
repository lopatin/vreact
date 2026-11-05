import { ensures, hole, type int } from "vreact/spec";

/** @trusted */
export function stub(x: int): int {
  ensures((r: int) => r < 0 - 100);
  return 0 - 101;
}

// proved by Lean, but relative to stub's (assumed) contract
export function viaStub(x: int): int {
  ensures((r: int) => r < 0 - 50);
  return hole<int>();
}

// proved outright
export function inc(x: int): int {
  ensures((r: int) => r === x + 1);
  return hole<int>();
}
