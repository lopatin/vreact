// expect: reject a Set element needs equality: constrain T, e.g. T extends int | string
// As GxMxRejectKeyUnconstrained, for a Set built in a generic body (`T extends {}` constrains
// nothing either).
import { type int } from "vreact/spec";

export function count<T extends {}>(xs: readonly T[]): int {
  return new Set<T>(xs).size;
}
