// expect: reject interface P is declared 2 times
// TypeScript merges the declarations of an interface (P has a and b): the translation reads one
// declaration at a time (formerly: "duplicate type name P").
import { type int } from "vreact/spec";

interface P {
  readonly a: int;
}
interface P {
  readonly b: int;
}

export function sum(p: P): int {
  return p.a + p.b;
}
