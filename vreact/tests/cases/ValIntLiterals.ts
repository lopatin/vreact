// expect: fail postcondition
// Integer literals and untyped locals are Lean `Int`, never `Nat` (where 0 - 1 = 0): in JS
// `pos - 1 >= 0` is false here, so the postcondition must fail.
import { ensures } from "vreact/spec";

export function canMoveLeft(): boolean {
  ensures((r: boolean) => r === true);
  const pos = 0;
  return pos - 1 >= 0;
}
