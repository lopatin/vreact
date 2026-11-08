// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { type int } from "vreact/spec";

type Box = { readonly m: ReadonlyMap<int, int> };
export function f(): Box {
  const n = new Map<int, int>();
  const b: Box = { m: n };
  n.set(1, 2);
  return b;
}
