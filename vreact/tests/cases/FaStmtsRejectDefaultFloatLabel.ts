// expect: reject case 1.5 can never match: `n` is an int, and 1.5 is not an integer
// The labels grouped with `default` are translated like the others (formerly never looked at, so
// this dead label was accepted silently).
import { type int } from "vreact/spec";
export function h(n: int): int {
  switch (n) {
    case 0:
      return 1;
    case 1.5:
    default:
      return 0;
  }
}
