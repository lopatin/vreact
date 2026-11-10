// expect: verified RATE=verified INF=verified HALF=verified NEG=verified
// An unannotated top-level constant is typed by its literal's value (finding numbers-r1-4): a
// negated literal was always an int, and `1e400` (which TypeScript reads as Infinity) too, so
// `const RATE = -2.5` was rejected ("type mismatch: expected int, got number").
import { ensures, type int } from "vreact/spec";

const RATE = -2.5;
const INF = 1e400;
const HALF = +0.5;
const NEG = -3;

export function scale(x: number): number {
  return x * RATE;
}
export function cap(x: number): number {
  return Math.min(x, INF);
}
export function half(x: number): number {
  return x * HALF;
}
export function neg(): int {
  ensures((r: int) => r === -3);
  return NEG;
}
