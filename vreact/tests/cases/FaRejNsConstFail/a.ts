// expect: fail postcondition
// `L.K` is lib's K (2), not 3: the postcondition fails (the namespace member is the
// module's export, also next to a local constant of the same name).
import { type int, ensures } from "vreact/spec";
import * as L from "./lib";

const K: int = 3;

export function f(): int {
  ensures((r) => r === K);
  return L.K;
}
