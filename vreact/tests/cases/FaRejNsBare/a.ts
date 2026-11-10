// expect: reject is the namespace object of a verified module
// The namespace object itself is not data: only its members are supported.
import { type int } from "vreact/spec";
import * as L from "./lib";

export function f(): int {
  const m = L;
  return m.K;
}
