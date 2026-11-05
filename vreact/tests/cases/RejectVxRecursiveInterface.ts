// expect: reject type Tree refers to itself: recursive types are not supported in VTS
import { type int } from "vreact/spec";
interface Tree {
  readonly v: int;
  readonly kid: Tree | null;
}
export function f(t: Tree): int {
  return t.v;
}
