import { ensures, type int } from "vreact/spec";
import { inc } from "./m";
export function twice(x: int): int {
  ensures((r: int) => r === x + 3);
  return inc(inc(x));
}
