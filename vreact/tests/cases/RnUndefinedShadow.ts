// expect: verified
// A local spelled `undefined` is that local, not JavaScript's undefined: builtins are recognised
// by the declaration a name resolves to, never by its spelling (formerly `return undefined`
// here was translated as `none`, and `r === undefined` was proved although f returns 3).
import { type int, ensures } from "vreact/spec";

export function f(): int | undefined {
  ensures((r) => r === 3);
  const undefined = 3;
  return undefined;
}

// the global undefined is still undefined
export function g(b: boolean): int | undefined {
  ensures((r) => (b ? r === undefined : r === 1));
  return b ? undefined : 1;
}
