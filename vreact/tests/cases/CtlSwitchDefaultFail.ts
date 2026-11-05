// expect: fail postcondition
// `default` before a case does not swallow it: a square has area 4 and blue has code 3,
// so these (false) postconditions must not be provable.
import { ensures, type int } from "vreact/spec";

type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "square"; readonly s: int } | { readonly kind: "dot" };
type Color = "red" | "green" | "blue";

export function ctlAreaMid(sh: Shape): int {
  ensures((a: int) => a !== 4);
  switch (sh.kind) {
    case "circle":
      return 3;
    default:
      return 0;
    case "square":
      return 4;
  }
}

export function ctlCodeMid(c: Color): int {
  ensures((n: int) => n !== 3);
  switch (c) {
    case "red":
      return 1;
    default:
      return 0;
    case "blue":
      return 3;
  }
}
