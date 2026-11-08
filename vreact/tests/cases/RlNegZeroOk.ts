// expect: verified halfOf=verified scaled=verified ratio=verified share=verified mean=verified signFree=verified
// Divisions that are exact although VTS values do not keep the sign of zero (round-1 finding
// r4-lean-negzero): a nonzero literal divisor (also negative, fractional, or a const initialised
// with one) needs no obligation; an int or number divisor needs `!== 0`, from a precondition or a
// guard (`d === 0 ? … : n / d`: -0 === 0). Everything but a division by a zero gives equal
// results for 0 and -0, so `-x`, `*`, `%` stay as they are.
import { ensures, requires, type int } from "vreact/spec";

const SCALE: int = 100;
const RATE: number = -2.5;

export function halfOf(x: number): number {
  return x / 2 + x / -0.5 + x / 1e3;
}

export function scaled(n: int): number {
  return n / SCALE + n / RATE;
}

export function ratio(a: int, b: int): boolean {
  requires(b > 0);
  ensures((r: boolean) => r === (a / b < 0.5));
  return a / b < 0.5;
}

export function share(part: number, whole: number): number {
  return whole === 0 ? 0 : part / whole;
}

export function mean(total: int, count: int): number {
  requires(count !== 0);
  return -total / (count * 2);
}

export function signFree(x: int, k: int): boolean {
  ensures((r: boolean) => r === (0 - x * k === -(x * k)));
  return -x * k === 0 - x * k;
}
