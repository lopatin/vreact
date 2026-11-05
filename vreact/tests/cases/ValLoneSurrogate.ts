// expect: fail postcondition
// "\uD800" and "\uDC00" are different one-code-unit strings (not both U+FFFD).
import { ensures } from "vreact/spec";

const HIGH: string = "\uD800";
const LOW: string = "\uDC00";

export function sameUnit(): boolean {
  ensures((r: boolean) => r === true);
  return HIGH === LOW;
}
