import { ensures, type int } from "vreact/spec";
import { inc } from "./m";
export function hasOne(x: int): boolean {
  ensures((r: boolean) => r === true);
  return [inc(0)].includes(x);
}
