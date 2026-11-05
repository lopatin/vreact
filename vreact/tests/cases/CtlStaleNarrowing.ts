// expect: fail postcondition
// Reassigning a narrowed `let` ends its narrowing (also after the if, and across a loop):
// each function returns p + 1 or a list element in JS, so `r === p` must not be provable.
import { ensures, type int } from "vreact/spec";

export function ctlBumped(p: int): int {
  ensures((r: int) => r === p);
  let x: int | null = p;
  if (x !== null) {
    const q: int = p + 1;
    x = q;
    return x;
  }
  return p;
}

export function ctlAfterIf(p: int): int | null {
  ensures((r: int | null) => r === p);
  let x: int | null = p;
  if (x !== null) {
  }
  const q: int = p + 1;
  x = q;
  return x;
}

export function ctlLoopNarrow(p: int, ys: readonly int[]): int | null {
  ensures((r: int | null) => r === p);
  let x: int | null = p;
  if (x !== null) {
    for (const y of ys) {
      x = y;
    }
    return x;
  }
  return p;
}
