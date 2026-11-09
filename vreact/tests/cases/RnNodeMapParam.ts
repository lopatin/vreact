// expect: reject parameter m has a React node (ReactNode / JSX.Element), which is not data
// React nodes inside a Map value (an array of them): not data.
import type { ReactNode } from "react";
import { type int } from "vreact/spec";

export function g(m: ReadonlyMap<int, readonly ReactNode[]>): int {
  return m.size;
}
