// expect: fail postcondition ok=verified
// False controls for the enum case split: a wrong arm, and a union arm with the wrong field.
import { ensures, type int } from "vreact/spec";

type Color = "red" | "green" | "blue";

export function wrongArm(c: Color): int {
  ensures((n: int) => (c === "red" && n === 1) || (c === "green" && n === 0) || (c === "blue" && n === 3));
  if (c === "red") return 1;
  if (c === "blue") return 2;
  return 0;
}

type T = { kind: "a" } | { kind: "b"; p: int; v: int } | { kind: "c"; v: int; q: int };

export function wrongField(t: T): int {
  ensures((r: int) => t.kind === "a" || (t.kind === "c" && r === t.q) || (t.kind === "b" && r === t.v));
  if (t.kind === "a") return 0;
  return t.v;
}

export function ok(c: Color): int {
  ensures((n: int) => (c === "red" && n === 1) || (c !== "red" && n === 0));
  return c === "red" ? 1 : 0;
}
