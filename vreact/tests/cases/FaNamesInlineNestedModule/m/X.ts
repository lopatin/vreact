import { ensures, type int } from "vreact/spec";
export function a(): int {
  ensures((r) => r === 1);
  return 1;
}
