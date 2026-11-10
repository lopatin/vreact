// expect: verified
// Unary + on numbers is the identity; int contracts use mathematical equality.
import { ensures, requires, type int } from "vreact/spec";

export function plus(x: int): int {
  ensures((r: int) => r === x);
  return +x;
}

export function neg(): int {
  ensures((r: int) => r < 0);
  const k: int | null = -3;
  return k ?? 0;
}

// (a division needs a divisor that is not zero: 1 / 0 is Infinity, 1 / -0 is -Infinity)
export function ratio(a: int, b: int): number {
  requires(b !== 0);
  return +(a / b);
}
