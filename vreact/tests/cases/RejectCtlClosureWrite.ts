// expect: reject assigning it from inside a function or callback is not supported
// The helper's write to the outer `let` was silently dropped (JS returns 1).
import { ensures, type int } from "vreact/spec";
export function ctlWriteInside(): int {
  ensures((r: int) => r === 0);
  let x: int = 0;
  const bump = (): int => {
    x = x + 1;
    return x;
  };
  const a = bump();
  return x;
}
