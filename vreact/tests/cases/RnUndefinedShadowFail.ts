// expect: fail postcondition
// What the old spelling-based translation proved: f returns its local `undefined`, which is 3,
// so `f() === undefined` (the global undefined here) is false in JS.
import { type int, ensures } from "vreact/spec";

function f(): int | undefined {
  const undefined = 3;
  return undefined;
}

export function g(): boolean {
  ensures((r) => r);
  return f() === undefined;
}
