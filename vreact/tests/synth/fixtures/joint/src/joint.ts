import { requires, ensures, hole, type int } from "vreact/spec";

export type Counter = { readonly total: int; readonly ops: int };
export type Action = { readonly kind: "add"; readonly amount: int } | { readonly kind: "reset" };

// two holes in one function: the postcondition is only checked once both are filled
export function bucket(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  if (x <= 100) return hole<int>();
  return hole<int>();
}

// one hole per case of a reducer: inputs reaching the other case are skipped while testing
export function step(s: Counter, a: Action): Counter {
  ensures((r: Counter) => r.ops === s.ops + 1);
  switch (a.kind) {
    case "add":
      return hole<Counter>();
    case "reset":
      return hole<Counter>();
  }
}

// backtracking: `xs` passes the tests for hole 1 (random arrays have at most 3 elements), Lean rejects it
export function cap(xs: readonly int[], flag: boolean): readonly int[] {
  ensures((r: readonly int[]) => r.length <= 3);
  if (flag) return hole<readonly int[]>();
  return hole<readonly int[]>();
}
