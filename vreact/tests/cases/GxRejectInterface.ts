// expect: reject generic interfaces are not supported in VTS
// Generic interfaces are rejected like generic type aliases.
import { ensures, requires, type int } from "vreact/spec";

interface Box<T> {
  readonly v: T;
}
export function unbox(b: Box<int>): int {
  return b.v;
}
