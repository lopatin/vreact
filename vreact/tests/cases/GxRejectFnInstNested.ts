// expect: reject id: its type parameter T would be ReadonlyMap<int, readonly (() => int)[]>, which has the function type () => int: not data
// A function type nested in an explicit type argument of a generic call (inside a Map value):
// rejected like a direct one (only `T = () => int` itself was checked).
import { type int } from "vreact/spec";

export function id<T>(x: T): T {
  return x;
}

export function g(): int {
  return id<ReadonlyMap<int, readonly (() => int)[]>>(new Map()).size;
}
