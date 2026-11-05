// expect: verified
// Several requires form one precondition; later ones may use earlier ones (guards).
import { requires, ensures, type int } from "vreact/spec";

export function sub(a: int, b: int): int {
  requires(a >= 0);
  requires(b >= 0);
  ensures((r: int) => r === a - b);
  return a - b;
}

export function use2(x: int): int {
  requires(x >= 0);
  return sub(x, 1);
}

export function head(xs: readonly int[]): int {
  requires(xs.length > 0);
  requires(xs[0] >= 0);
  ensures((r: int) => r >= 0);
  return xs[0];
}

export function callHead(): int {
  ensures((r: int) => r === 3);
  return head([3, 4]);
}
