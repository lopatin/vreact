// expect: fail nonzero-divisor only=incomplete grouped=incomplete
// A switch with no label outside the default group still evaluates its discriminant (once): its
// obligation is checked (formerly reported "missing from the generated Lean (translator bug)").
import { idiv, type int } from "vreact/spec";
export function only(d: int): int {
  switch (idiv(10, d)) {
    default:
      return 1;
  }
}
export function grouped(d: int): int {
  switch (idiv(10, d)) {
    case 5:
    default:
      return 0;
  }
}
