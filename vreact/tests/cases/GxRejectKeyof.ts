// expect: reject keyof is not supported
// keyof constraints are not supported.
import { ensures, requires, type int } from "vreact/spec";

type Item = { readonly a: int; readonly b: int };
export function key<K extends keyof Item>(k: K): K {
  return k;
}
