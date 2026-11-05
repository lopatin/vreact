// expect: reject the bitwise operator >>= is not supported in VTS
// A compound bitwise assignment statement (formerly "expression statement has no effect").
import { type int } from "vreact/spec";
export function f(x: int): int {
  let y = x;
  y >>= 1;
  return y;
}
