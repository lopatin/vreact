// expect: verified
// An unannotated array literal (and a conditional) is typed by the join of its elements' types,
// as TypeScript does (finding mapset-r1-3): `[c, "zzz"]` was typed Color[] from its first
// element and rejected ('"zzz" is not a member of Color'), `[x, 2.5]` ("expected int, got
// number"). An enum member is widened to its string, an int to a number.
import { ensures, type int } from "vreact/spec";

export type Color = "red" | "green";

export function hasOther(c: Color): boolean {
  ensures((r: boolean) => r);
  const s = new Set([c, "zzz"]);
  return s.has("zzz") && s.has(c);
}
export function nums(x: int): readonly number[] {
  ensures((r: readonly number[]) => r.length === 2);
  const xs = [x, 2.5];
  return xs;
}
export function other(c: Color, b: boolean): string {
  ensures((r: string) => b ? r === c : r === "zzz");
  const t = b ? c : "zzz";
  return t;
}
// a member literal keeps the enum type, as in TypeScript (unchanged)
export function orRed(c: Color, b: boolean): Color {
  ensures((r: Color) => b ? r === c : r === "red");
  const d = b ? c : "red";
  return d;
}
// an array whose first element needs a type from the others
export function nested(): readonly (readonly int[])[] {
  ensures((r: readonly (readonly int[])[]) => r.length === 2 && r[1].length === 1);
  const xss = [[], [1]];
  return xss;
}
