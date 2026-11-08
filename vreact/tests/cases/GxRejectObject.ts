// expect: reject `object` says nothing about the fields
// `extends object` names no fields: a field constraint lists them.
import { ensures, requires, type int } from "vreact/spec";

export function id<T extends object>(x: T): T {
  return x;
}
