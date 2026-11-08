// expect: fail index viaShorthand=incomplete direct=incomplete why.viaShorthand=uses~B why.direct=uses~B
// B's index obligation fails; a function that reads B only through a shorthand property
// `{ B, c }` uses B like one that writes `{ B: B, c }` (formerly: "depends on sorryAx, but Lean
// reported no failure or sorry it could come from", its dependency on B not followed).
import { type int, ensures } from "vreact/spec";

const XS: readonly int[] = [1, 2];
export const B: int = XS[5];

type P = { readonly B: int; readonly c: int };
export function viaShorthand(c: int): P {
  ensures((r) => r.c === c);
  return { B, c };
}

export function direct(c: int): P {
  ensures((r) => r.c === c);
  return { B: B, c };
}
