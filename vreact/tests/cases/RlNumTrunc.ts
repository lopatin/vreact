// expect: fail postcondition failtext=Num.trunc
// Math.trunc on a number is the opaque `VReact.JS.Num.trunc` (R4 item 14; before: Lean's
// `Float.round`, a different function: Math.trunc(2.7) is 2, Float.round 2.7 is 3). Nothing is
// known about it, so this (true) ensures is not provable: the failure shows `Num.trunc`.
import { ensures } from "vreact/spec";
export function tr(): number {
  ensures((r: number) => r === 2);
  return Math.trunc(2.7);
}
