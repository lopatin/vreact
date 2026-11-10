// expect: fail postcondition strOfSum=incomplete sliceLit=incomplete atLit=incomplete trimLit=incomplete label=incomplete
// False closed facts stay failed (numbers-r1-5): evaluation decides them false.
import { ensures, type int } from "vreact/spec";

export function strOfSum(): boolean {
  ensures((r: boolean) => r);
  return String(1 + 2) === "4";
}
export function sliceLit(): boolean {
  ensures((r: boolean) => r);
  return "abc".slice(-2) === "ab";
}
export function atLit(): boolean {
  ensures((r: boolean) => r);
  return [1, 2, 3].at(-1) === 2;
}
export function trimLit(): boolean {
  ensures((r: boolean) => r);
  return " x ".trim() === " x";
}
export function label(n: int): string {
  ensures((r: string) => r === "n=3");
  return n === 2 ? `n=${n + 2}` : "n=3";
}
