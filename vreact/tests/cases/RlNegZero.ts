// expect: fail nonzero-divisor negDiv=incomplete prodDiv=incomplete remDiv=incomplete truncDiv=incomplete floorDiv=incomplete idivDiv=incomplete minDiv=incomplete viaNumber=incomplete lit=incomplete neg=verified
// An int that is 0 may be -0 in JS (round-1 finding r4-lean-negzero): `-x`, `a * b`, `a % b`,
// `Math.trunc(a / b)`, `Math.floor(0 / -5)`, `idiv`, `Math.min(0, -0)` and the literal `-0` give
// -0, and 1 / -0 is -Infinity where 1 / 0 is Infinity. Lean's Int has one zero, so these false
// ensures (each compares 1 / -0 > 0, false in JS, with 1 / 0 > 0, true) were VERIFIED: both
// sides were the same Lean term. VTS values are JS values up to the sign of zero now, and a
// division needs a divisor that is not zero (an obligation, which fails here); so does the
// ensures' own division. `neg` shows -0 itself is harmless: -0 === 0.
import { ensures, requires, idiv, type int } from "vreact/spec";

export function neg(x: int): int {
  ensures((r: int) => r === 0 - x);
  return -x;
}

export function negDiv(x: int): boolean {
  requires(x === 0);
  ensures((r: boolean) => r === (1 / x > 0));
  return 1 / -x > 0;
}

export function prodDiv(x: int): boolean {
  requires(x === 0);
  ensures((r: boolean) => r === (1 / x > 0));
  return 1 / (-3 * x) > 0;
}

// -4 % 2 is -0
export function remDiv(a: int): boolean {
  requires(a === -4);
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / (a % 2) > 0;
}

// Math.trunc(-1 / 2) is -0
export function truncDiv(a: int, b: int): boolean {
  requires(a === -1 && b === 2);
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / Math.trunc(a / b) > 0;
}

// Math.floor(0 / -5) is Math.floor(-0), -0
export function floorDiv(): boolean {
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / Math.floor(0 / -5) > 0;
}

export function idivDiv(): boolean {
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / idiv(0, -5) > 0;
}

export function minDiv(): boolean {
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / Math.min(0, -0) > 0;
}

// through a number variable
export function viaNumber(x: int): boolean {
  requires(x === 0);
  ensures((r: boolean) => r === (1 / x > 0));
  const y: number = -x;
  return 1 / y > 0;
}

export function lit(): boolean {
  ensures((r: boolean) => r === (1 / 0 > 0));
  return 1 / -0 > 0;
}
