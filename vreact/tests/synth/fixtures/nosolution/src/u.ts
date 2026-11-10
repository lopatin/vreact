import { ensures, hole, type int } from "vreact/spec";

// unsatisfiable: the diagnostics must say how far the search went and why it stopped
export function impossible(x: int): int {
  ensures((r: int) => r > x && r < x);
  return hole<int>();
}
