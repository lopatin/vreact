// expect: fail precondition pick=verified bad=incomplete good=verified
// The precondition of a generic function, instantiated at the call, is an obligation there.
import { requires, ensures, type int } from "vreact/spec";

export function pick<T>(xs: readonly T[], i: int): T {
  requires(0 <= i && i < xs.length);
  return xs[i];
}

export function good(xs: readonly string[]): string {
  requires(xs.length > 1);
  return pick(xs, 1);
}

export function bad(xs: readonly string[]): string {
  return pick(xs, 0);
}
