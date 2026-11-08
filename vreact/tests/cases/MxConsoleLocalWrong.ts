// expect: fail postcondition
import { ensures, type int } from "vreact/spec";

// wrong: `console.add(1)` on a local Set named `console` adds to it (it is not logging)
export function one(): int {
  ensures((r) => r === 0);
  const console = new Set<int>();
  console.add(1);
  return console.size;
}
