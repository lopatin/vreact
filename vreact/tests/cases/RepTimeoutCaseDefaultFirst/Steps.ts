// expect: fail postcondition failtext=then~case~h_3.isFalse~failed failtext=one~per~`case`~label,~in~the~order~written,~then~one~for~the~rest:~`default`,~wherever~it~is~written verdict=not-verified
// The case named after a timeout (`timeoutCases`) is Lean's name for it, and the report says how
// to read it: a `switch` on a union is a `match` with one alternative per `case` label in the order
// written, then one for `default`, wherever it is written. Here `default` is written first and "a"
// and "b" share a body, so the false "d" arm (an offset below 40 moves while paused) is the third
// alternative, `h_3`, not the third clause as written (`case "b"`). The variable `a` is substituted
// away in the case's goal, so the name is the only pointer to the arm.
// (Heartbeat counts are deterministic; a change of the automation may move the case a little.)
import { ensures, implies, type int } from "vreact/spec";
type Feed = { readonly offset: int; readonly seed: int };
type A = { readonly kind: "a" } | { readonly kind: "b" } | { readonly kind: "c" } | { readonly kind: "d" };
export function nextSeed(s: int): int {
  return (s * 75 + 74) % 65537;
}
export function walk(f: Feed): Feed {
  const seed = nextSeed(f.seed);
  const move = (seed % 5) - 2;
  const next = f.offset + move;
  return { offset: next > 40 || next < -40 ? f.offset - move : next, seed: seed };
}
export function step(f: Feed, paused: boolean, a: A): Feed {
  ensures((r: Feed) => implies(paused, r.offset === f.offset && r.seed === f.seed));
  switch (a.kind) {
    default:
      return f;
    case "a":
    case "b":
      return walk(f);
    case "d":
      return f.offset >= 40 ? f : { ...f, offset: f.offset + 1 };
  }
}
