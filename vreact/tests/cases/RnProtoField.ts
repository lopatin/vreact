// expect: reject a field named `__proto__` is not supported
// In an object literal `{ __proto__: 5 }` sets the prototype (ECMA-262 B.3.1: to nothing, 5 is
// not an object) and creates no property; `o.__proto__` then reads Object.prototype. Formerly
// VERIFIED with r === 5.
import { type int, ensures } from "vreact/spec";

type R = { readonly __proto__: int };

export function f(): int {
  ensures((r) => r === 5);
  const o: R = { __proto__: 5 };
  return o.__proto__;
}
