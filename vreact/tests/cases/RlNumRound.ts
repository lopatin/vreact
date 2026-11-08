// expect: fail postcondition failtext=x.round.lt
// Math.round on a number is the opaque `VReact.JS.Num.round` (R4 item 13; before: the
// transparent `floor(x + 0.5)`, which is not Math.round: Math.round(0.49999999999999994) is 0,
// floor(0.49999999999999994 + 0.5) is 1, and Math.round(-0.5) is -0). A proof could unfold it.
import { ensures } from "vreact/spec";
export function rd(x: number): boolean {
  ensures((r: boolean) => r === (Math.floor(x + 0.5) < 1));
  return Math.round(x) < 1;
}
