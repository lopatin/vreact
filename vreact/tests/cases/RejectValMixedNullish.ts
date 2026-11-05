// expect: reject compares values that may be null and undefined
// null === undefined is false in JS, but both are absent values in VTS.
import { type int } from "vreact/spec";

type Item = { readonly id: int; readonly parent?: int };

export function sameParent(a: int | null, i: Item): boolean {
  return a === i.parent;
}
