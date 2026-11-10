// expect: reject a /** @trusted */ generic function (decode<T>) is not supported: Lean would assume its type and contracts for every type T
// A @trusted generic function would be a Lean axiom for every Lean type: `decode (T := Empty)`
// inhabits Empty (False), although decode only ever runs at the types JS calls it with.
import { type int } from "vreact/spec";

/** @trusted */
export function decode<T>(s: string): T {
  return JSON.parse(s) as T;
}

export function count(s: string): int {
  return decode<int>(s);
}
