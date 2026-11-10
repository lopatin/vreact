// expect: verified
// A function may read a constant declared below it (it runs later), also through a shorthand
// property `{ B, c }`: the Lean declarations are ordered by what each one reads, the shorthand
// property's variable included (formerly g came before B in Lean: an unknown identifier).
import { type int, ensures } from "vreact/spec";

type P = { readonly B: int; readonly c: int };
export function g(c: int): P {
  ensures((r) => r.B + r.c === c + 2);
  return { B, c };
}
export const B: int = 2;

type Box = { readonly max: int };
function mk(n: int): Box {
  const r: Box = { max: n };
  return r;
}
export const LIMIT: Box = mk(B + 1);
export function limit(): int {
  ensures((r) => r === 3);
  return LIMIT.max;
}
