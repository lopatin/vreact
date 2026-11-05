import { ensures, type int } from "vreact/spec";
import { b } from "./a";
import { post } from "./a/b";
export function combine(x: int): int {
  ensures((r: int) => r > x);
  return b(post(x));
}
