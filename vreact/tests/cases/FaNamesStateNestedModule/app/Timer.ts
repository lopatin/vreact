import { ensures, type int } from "vreact/spec";
export function left(): int {
  ensures((r) => r === 10);
  return 10;
}
