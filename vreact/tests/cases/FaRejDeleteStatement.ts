// expect: reject removes the property from the object, which its other users see (VTS data is immutable)
// `delete p.note;` mutates the caller's object (formerly: "expression statement has no effect").
import { type int } from "vreact/spec";
export function f(p: { note?: string }): boolean {
  delete p.note;
  return p.note === undefined;
}
