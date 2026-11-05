// expect: verified
// switch: `default` in any position, `default` grouped with case labels, and braced
// case bodies ending in `break` — on unions, enums and strings.
import { ensures, type int } from "vreact/spec";

type Shape = { readonly kind: "circle"; readonly r: int } | { readonly kind: "square"; readonly s: int } | { readonly kind: "dot" };
type Color = "red" | "green" | "blue";

export function ctlArea(sh: Shape): int {
  ensures((a: int) => a >= 0);
  switch (sh.kind) {
    case "circle":
      return 3;
    default:
      return 0;
    case "square":
      return 4;
  }
}

export function ctlSides(sh: Shape): int {
  ensures((n: int) => n >= 0);
  switch (sh.kind) {
    case "square":
      return 4;
    case "circle":
    default:
      return 0;
  }
}

export function ctlCode(c: Color): int {
  ensures((n: int) => n >= 0);
  switch (c) {
    case "red":
      return 1;
    default:
    case "green":
      return 0;
    case "blue":
      return 3;
  }
}

export function ctlStep(sh: Shape): int {
  ensures((n: int) => n >= 1);
  let r: int = 1;
  switch (sh.kind) {
    case "circle": {
      const k: int = 2;
      r = k;
      break;
    }
    case "square":
    default: {
      r = 3;
      break;
    }
  }
  return r;
}

export function ctlScore(key: string): int {
  ensures((n: int) => n === 0 || n === 12);
  let r: int = 0;
  switch (key) {
    case "a": {
      const bonus: int = 2;
      r = 10 + bonus;
      break;
    }
    default:
      break;
  }
  return r;
}
