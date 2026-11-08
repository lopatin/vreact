// expect: reject `const` type parameters are not supported in VTS
// `const` type parameters infer literal types, which VTS does not model.
import { ensures, requires, type int } from "vreact/spec";

export function id<const T>(x: T): T {
  return x;
}
