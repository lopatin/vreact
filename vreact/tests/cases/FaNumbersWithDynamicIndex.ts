// expect: fail index dyn=incomplete faildesc=VTS~counts~an~index~from~the~end
/// <reference lib="es2023.array" />
// An index not written `-k` must be non-negative, stronger than JS (numbers-r1-3): the failed
// obligation says so instead of claiming that -1 is out of bounds.
import { requires, type int } from "vreact/spec";

export function dyn(xs: readonly int[], v: int): readonly int[] {
  requires(xs.length > 0);
  const i = -1;
  return xs.with(i, v);
}
