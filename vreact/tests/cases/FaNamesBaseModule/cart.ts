import { ensures } from "vreact/spec";
import { total, type Line } from "./Base";
export function prepend(xs: readonly Line[], l: Line): readonly Line[] {
  ensures((r: readonly Line[]) => total(r) === total(xs) + l.cents);
  return [l, ...xs];
}
