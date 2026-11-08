import { type int, ensures } from "vreact/spec";
import { A } from "./a";

export const B: int = A + 1;

export function two(): int {
  ensures((r) => r === 2);
  return B;
}
