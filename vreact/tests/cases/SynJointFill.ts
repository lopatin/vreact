// expect: verified
// What `vreact synth` now finds for functions with several holes (filled and proved together).
import { requires, ensures, type int } from "vreact/spec";

export type Counter = { readonly total: int; readonly ops: int };
export type Action = { readonly kind: "add"; readonly amount: int } | { readonly kind: "reset" };

export function bucket(x: int): int {
  requires(x >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  if (x <= 100) return 0;
  return 0;
}

export function step(s: Counter, a: Action): Counter {
  ensures((r: Counter) => r.ops === s.ops + 1);
  switch (a.kind) {
    case "add":
      return { ...s, ops: s.ops + 1 };
    case "reset":
      return { ...s, ops: s.ops + 1 };
  }
}

export function cap(xs: readonly int[], flag: boolean): readonly int[] {
  ensures((r: readonly int[]) => r.length <= 3);
  if (flag) return [];
  return [];
}
