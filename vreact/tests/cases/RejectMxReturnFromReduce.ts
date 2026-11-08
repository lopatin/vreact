// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { ensures, type int } from "vreact/spec";

// the reduce callback's `return { m: n }` stores `n` in the result; the later set changes b.m too
type Box = { readonly m: ReadonlyMap<int, int> };
export function f(): int {
  ensures((r) => r === 0);
  const n = new Map<int, int>();
  const init: Box = { m: new Map<int, int>() };
  const b = [0].reduce((acc: Box, x: int): Box => {
    return { m: n };
  }, init);
  n.set(1, 1);
  return b.m.size;
}
