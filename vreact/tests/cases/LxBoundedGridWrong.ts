// expect: fail postcondition ok=verified
// False controls for the board quantifiers: a strict bound on a 2-D grid, a -1 cell among nine.
import { requires, ensures, forall, type int } from "vreact/spec";

export function ok(g: readonly (readonly int[])[]): int {
  requires(g.length === 2 && forall(0, 2, (r) => g[r].length === 2 && forall(0, 2, (c) => g[r][c] >= 0)));
  ensures((v: int) => v >= 0);
  return g[0][1];
}
export function badCorner(g: readonly (readonly int[])[]): int {
  requires(g.length === 2 && forall(0, 2, (r) => g[r].length === 2 && forall(0, 2, (c) => g[r][c] >= 0)));
  ensures((v: int) => v > 0);
  return g[1][1];
}
export function badNine(): readonly int[] {
  ensures((r: readonly int[]) => r.length === 9 && forall(0, 9, (i) => r[i] >= 0));
  return [0, 0, 0, 0, 0, 0, 0, 0, -1];
}
