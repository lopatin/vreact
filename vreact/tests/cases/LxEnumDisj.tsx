// expect: verified
// N11: true disjunctive postconditions/invariants over an enumeration or a discriminated union
// need a case split on the enum value, which `grind` does not do itself (vreact_finish splits
// a small enum/union of the goal as a fallback, up to two levels).
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

type Color = "red" | "green" | "blue";

export function ifChain(c: Color): int {
  ensures((n: int) => (c === "red" && n === 1) || (c === "green" && n === 0) || (c === "blue" && n === 3));
  if (c === "red") return 1;
  if (c === "blue") return 3;
  return 0;
}

type T = { kind: "a" } | { kind: "b"; p: int; v: int } | { kind: "c"; v: int; q: int };

export function getV(t: T): int {
  ensures((r: int) => t.kind === "a" || (t.kind === "c" && r === t.v) || (t.kind === "b" && r === t.v));
  if (t.kind === "a") return 0;
  return t.v;
}

// two enumerations: the split goes two levels deep
type Size = "s" | "m" | "l";
export function price(c: Color, s: Size): int {
  ensures((p: int) => (s === "s" && p < 10) || (s === "m" && 10 <= p && p < 20) || (s === "l" && p >= 20));
  const base = s === "s" ? 5 : s === "m" ? 12 : 25;
  return c === "red" ? base + 1 : base;
}

// an enumeration in state: the invariant is a three-way disjunction
type Mode = "idle" | "busy" | "done";
export function Job() {
  const [mode, setMode] = useState<Mode>("idle");
  const [n, setN] = useState<int>(0);
  invariant((mode === "idle" && n === 0) || (mode === "busy" && n > 0) || mode === "done");
  return (
    <div>
      <button onClick={() => { if (mode === "idle") { setMode("busy"); setN(1); } }}>start</button>
      <button onClick={() => { if (mode === "busy") setN(n + 1); }}>step</button>
      <button onClick={() => setMode("done")}>finish</button>
    </div>
  );
}
