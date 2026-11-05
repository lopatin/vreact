// expect: verified f=verified typed=verified pick=verified
// V2 (translator crash): a variant whose tag is the name of the discriminant (`{ type: "type" }`),
// or of a field all variants share (`{ type: "n"; n: int }`), declared the constructor and the
// accessor `A.type` / `A.n` twice; so did the tags "rec" and "rec'" (Lean's `rec` is primed).
import { ensures, type int } from "vreact/spec";

type A = { type: "type"; n: int } | { type: "clear"; n: int } | { type: "n"; n: int };
export function f(a: A): int {
  ensures((r: int) => (a.type === "type" && r === a.n) || (a.type !== "type" && r === 0));
  return a.type === "type" ? a.n : 0;
}

type Act = { type: "type"; text: string } | { type: "clear" };
type St = { text: string; edits: int };
export function typed(s: St, a: Act): St {
  ensures((r: St) => r.edits === s.edits + 1);
  switch (a.type) {
    case "type":
      return { text: s.text + a.text, edits: s.edits + 1 };
    case "clear":
      return { text: "", edits: s.edits + 1 };
  }
}
export function mk(): Act {
  ensures((r: Act) => r.type === "type");
  return { type: "type", text: "x" };
}

type R = { kind: "rec"; x: int } | { kind: "rec'"; y: int };
export function pick(r: R): int {
  ensures((v: int) => (r.kind === "rec" && v === 1) || (r.kind === "rec'" && v === 2));
  return r.kind === "rec" ? 1 : 2;
}
