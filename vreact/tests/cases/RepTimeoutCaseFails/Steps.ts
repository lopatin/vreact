// expect: fail postcondition failtext=then~case~h_2.isFalse~failed failtext=h~:~¬40~≤~f.offset faildesc=postcondition~of~step verdict=not-verified
// A false postcondition of a function that switches on `a.kind` runs out of its budget (the
// "walk" case puts the random walk's arithmetic in scope, as in step 33 of the options-chain
// walkthrough). After the timeout, each case is tried alone (`timeoutCases`): the report names
// the case that fails — the "bump" arm, `h_2`, when the offset is below 40 — and shows its goal.
// (Heartbeat counts are deterministic; a change of the automation may move the case a little.)
import { ensures, implies, type int } from "vreact/spec";
type Feed = { readonly offset: int; readonly seed: int };
type A = { readonly kind: "walk" } | { readonly kind: "bump" } | { readonly kind: "stay" };
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
    case "walk":
      return walk(f);
    case "bump":
      return f.offset >= 40 ? f : { ...f, offset: f.offset + 1 };
    case "stay":
      return f;
  }
}
