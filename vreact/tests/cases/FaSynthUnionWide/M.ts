// expect: synth seconds=10 mk=- out=time~limit~was~reached~at~size~9 maxsecs=180
// synth round 2: the candidates of one size were all built before the first was tested, and the
// time limit was checked only between candidates: a variant literal with 8 int fields has 10^8
// combinations at size 9, whose list exhausted the heap ("JavaScript heap out of memory", the run
// crashed). Candidates are now built as they are tested, so the time limit (10 s here) holds.
import { ensures, hole, type int } from "vreact/spec";

export type Shape =
  | { readonly kind: "none" }
  | { readonly kind: "box"; readonly a: int; readonly b: int; readonly c: int; readonly d: int; readonly e: int; readonly f: int; readonly g: int; readonly h: int };

export function mk(p1: int, p2: int, p3: int, p4: int, p5: int, p6: int, p7: int, p8: int): Shape {
  ensures((s: Shape) => s.kind === "box" && s.a === p1 + p2 + p3);
  return hole<Shape>();
}
