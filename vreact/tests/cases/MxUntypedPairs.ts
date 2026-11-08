// expect: verified
import { ensures, type int } from "vreact/spec";

// a literal of [key, value] pairs needs no type arguments: the types come from its first pair
export function mxupGet(): string {
  ensures((r) => r === "b");
  const m = new Map([[1, "a"], [2, "b"]]);
  return m.get(2) ?? "";
}

// a repeated key keeps its first position and takes its last value
export function mxupDup(): readonly string[] {
  ensures((r: readonly string[]) => r.length === 2 && r[0] === "x" && r[1] === "y");
  const m = new Map([["x", 1], ["y", 2], ["x", 3]]);
  return [...m.keys()];
}

export function mxupLast(): int {
  ensures((r) => r === 3);
  const m = new Map([["x", 1], ["y", 2], ["x", 3]]);
  return m.get("x") ?? 0;
}
