// expect: verified
// A guard `xs.length === 3 && forall(0, 3, i => xs[i] >= 0)` puts `∀ i (h : 0 ≤ i) (h' : i < 3),
// … xs[i]'… …` into the context of every obligation of the function. On that shape `grind` (Lean's
// arithmetic normaliser under a binder with a literal bound) raises `maximum recursion depth`, a
// runtime exception `first`/`try` do not catch: the index obligations below used to fail with it
// instead of falling back to the other strategies (here `omega` on the unpacked guard).
import { requires, ensures, forall, type int } from "vreact/spec";

export function sum3(xs: readonly int[]): int {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0));
  ensures((r: int) => r === xs[0] + xs[1] + xs[2]);
  return xs[0] + xs[1] + xs[2];
}

export function middle(xs: readonly int[]): int {
  requires(xs.length === 3 && forall(0, 3, (i) => xs[i] >= 0));
  ensures((r: int) => r === xs[1]);
  const m = xs[1];
  return m;
}
