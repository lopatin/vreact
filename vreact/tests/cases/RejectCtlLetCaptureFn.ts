// expect: reject which is reassigned after the function is created
// A helper arrow called after the reassignment reads x === 5 in JS.
import { ensures, type int } from "vreact/spec";
export function ctlReadLater(): int {
  ensures((r: int) => r === 0);
  let x: int = 0;
  const get = (): int => x;
  x = 5;
  return get();
}
