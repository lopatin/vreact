// expect: verified
// String concatenation with an int, a boolean or an enum member operand: JS ToString, as in
// template literals (exact on ints: f(-5, "a") is "-5a").
import { ensures, type int } from "vreact/spec";
type Mode = "on" | "off";
export function f(x: int, s: string): string {
  ensures((r: string) => r === `${x}${s}`);
  return x + s;
}
export function g(s: string, x: int): string {
  ensures((r: string) => r === `${s}${x}`);
  return s + x;
}
export function h(x: int): string {
  // left to right: (x + 2) is an addition, the rest concatenations
  ensures((r: string) => r === `${x + 2}a-5true`);
  return x + 2 + "a" + -5 + true;
}
export function m(k: Mode): string {
  ensures((r: string) => r === `mode ${k}`);
  return "mode " + k;
}
export function acc(xs: readonly int[]): string {
  let s = "";
  for (const x of xs) {
    s += x;
  }
  return s;
}
