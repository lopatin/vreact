// expect: reject an optional field named `__lookupGetter__` is not supported
// Every object inherits `__lookupGetter__` (a function) from Object.prototype, and TypeScript's
// library does not declare it, so `{ id: 1 }` type-checks as an R without the field: reading
// it gives the inherited function, not undefined (formerly VERIFIED with r === true; JS: false).
import { type int, ensures } from "vreact/spec";

type R = { readonly id: int; readonly __lookupGetter__?: int };

export function f(): boolean {
  ensures((r) => r === true);
  const o: R = { id: 1 };
  return o.__lookupGetter__ === undefined;
}
