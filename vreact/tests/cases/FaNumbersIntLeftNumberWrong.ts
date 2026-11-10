// expect: fail postcondition pickLit=incomplete widened=incomplete
// The int widened to a number is that number (numbers-r1-2): nothing false becomes provable.
import { ensures, type int } from "vreact/spec";

export function pickLit(c: boolean, i: int): number {
  ensures((r: number) => r === 2.5);
  const t = c ? i : 2.5;
  return t;
}
export function widened(i: int, y: number): boolean {
  ensures((r: boolean) => r);
  return i < y;
}
