import { requires, ensures, hole, type int } from "vreact/spec";
import { type Level } from "./model";

export function capped(l: Level): int {
  requires(l.value >= 0);
  ensures((r: int) => 0 <= r && r <= 20);
  return hole<int>();
}
