// expect: reject the bitwise operator ~ is not supported in VTS
// (formerly reported as a misplaced ++/--)
import { ensures, type int } from "vreact/spec";
export function f(x: int): int {
  ensures((r: int) => r === -x - 1);
  return ~x;
}
