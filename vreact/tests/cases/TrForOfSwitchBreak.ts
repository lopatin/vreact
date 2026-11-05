// expect: verified
// A `break` that ends a switch case inside for…of only leaves the switch.
import { ensures, type int } from "vreact/spec";

type Op = { readonly kind: "add"; readonly n: int } | { readonly kind: "neg" } | { readonly kind: "skip" };
type Color = "red" | "green" | "blue";

export function run(ops: readonly Op[]): int {
  let acc: int = 0;
  for (const op of ops) {
    switch (op.kind) {
      case "add":
        acc += op.n;
        break;
      case "neg": {
        acc = -acc;
        break;
      }
      default:
        break;
    }
  }
  return acc;
}

export function reds(cs: readonly Color[]): int {
  let k: int = 0;
  for (const c of cs) {
    switch (c) {
      case "red":
        k += 1;
        break;
      case "green":
      case "blue":
        break;
    }
  }
  return k;
}

export function codes(xs: readonly int[]): int {
  let s: int = 0;
  for (const x of xs) {
    switch (x) {
      case 1:
        s += 1;
        break;
      default:
        s += 2;
        break;
    }
  }
  return s;
}

export function check(): int {
  ensures((r: int) => r === 6);
  return run([{ kind: "add", n: 2 }, { kind: "skip" }, { kind: "neg" }, { kind: "add", n: 5 }]) + reds(["red", "blue", "red"]) + codes([1, 5]) - 2;
}
