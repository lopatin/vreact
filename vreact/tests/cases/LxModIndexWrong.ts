// expect: fail postcondition index ok=verified
// False controls for `%`: in JS `-1 % 3 === -1` (the sign of the dividend), so a remainder is
// not a valid index unless the dividend is non-negative.
import { requires, ensures, type int } from "vreact/spec";

export function prevBad(xs: readonly int[], sel: int): int {
  requires(xs.length >= 2 && 0 <= sel && sel < xs.length);
  return xs[(sel - 1) % xs.length];
}

export function negNotPos(n: int, s: int): int {
  requires(n > 0);
  ensures((r: int) => 0 <= r);
  return (s - 5) % n;
}

export function ok(n: int, s: int): int {
  requires(n > 0 && s >= 5);
  ensures((r: int) => 0 <= r);
  return (s - 5) % n;
}
