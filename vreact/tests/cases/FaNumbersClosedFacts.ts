// expect: verified
// Closed facts about literals are decided by evaluation (finding numbers-r1-5): each was true in
// JS but failed with the unevaluated term in the goal (`¬JS.str 3 = { units := [51] }`).
import { ensures, type int } from "vreact/spec";

export function strOfSum(): boolean {
  ensures((r: boolean) => r);
  return String(1 + 2) === "3";
}
export function sliceLit(): boolean {
  ensures((r: boolean) => r);
  return "abc".slice(-2) === "bc";
}
export function atLit(): boolean {
  ensures((r: boolean) => r);
  return [1, 2, 3].at(-1) === 3;
}
export function joinLit(): boolean {
  ensures((r: boolean) => r);
  return ["a", "b"].join() === "a,b";
}
export function repeatLit(): boolean {
  ensures((r: boolean) => r);
  return "ab".repeat(2) === "abab";
}
export function trimLit(): boolean {
  ensures((r: boolean) => r);
  return " x ".trim() === "x";
}
// a value known from a test: substituted, then evaluated
export function label(n: int): string {
  ensures((r: string) => r === "n=3");
  return n === 2 ? `n=${n + 1}` : "n=3";
}
